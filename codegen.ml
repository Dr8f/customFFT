open Util
;;

open Lib
;;

open Code
;;

let _rs = Ctype.Env("RS")
;;

let _at = "at"
;;

let _compute = "compute"
;;

let _rule = Var(Ctype.Int, "_rule")
;;

let _dat = Var(Ctype.Ptr(Ctype.Complex), "_dat")
;;

let build_child_var (num:int) : expr =
  Var(Ctype.Ptr(_rs),"child"^(string_of_int num))
;;

let expr_of_intexpr (intexpr : Intexpr.intexpr) : expr =
  match intexpr with
    Intexpr.IConstant x -> IConst x
  | _ -> Var(Ctype.Int, Intexpr.string_of_intexpr intexpr)
;;

let _output = Var(Ctype.Ptr(Ctype.Complex),"Y")
;;

let _input = Var(Ctype.Ptr(Ctype.Complex),"X")
;;


let rec expr_of_idxfunc (idxfunc : Idxfunc.idxfunc) : expr =
  match idxfunc with
  | Idxfunc.FArg(cvar, _) -> Var(Ctype.Ptr(Ctype.ctype_of_cvar cvar), Ctype.name_of_cvar cvar)
  | Idxfunc.PreWrap(cvar, l, funcs, _) -> FunctionCall(Ctype.name_of_cvar cvar, ((List.map expr_of_intexpr l)@(List.map expr_of_idxfunc funcs)))
  | _ -> failwith("expr_of_idxfunc, not handled: "^(Idxfunc.string_of_idxfunc idxfunc))        		
;;


let rec code_of_func (func : Idxfunc.idxfunc) ((input,code):expr * code list) : expr * code list =
  print_string ("Processing "^(Idxfunc.string_of_idxfunc func)^"\n");
  match func with
  |Idxfunc.FH(_,_,b,s) -> let output = gen_var#get Ctype.Int "t" in
		      (output,code@[Declare(output);Assign(output, Plus((expr_of_intexpr b), Mul((expr_of_intexpr s),input)))])
  |Idxfunc.FD(n,k) -> let output = gen_var#get Ctype.Complex "c" in
		  (output,code@[Declare(output);Assign(output, FunctionCall("omega", [(expr_of_intexpr n);UniMinus(Mul(Mod(input,(expr_of_intexpr k)), Divide(input,(expr_of_intexpr k))))]))])
  |Idxfunc.FArg((_,Ctype.Func ctypes),mylist) ->
    (
      match last ctypes with
      |None -> failwith("empty type list")
      |Some x -> 
	let output = gen_var#get x "c" in
	(output,code@[Declare(output);Assign(output, MethodCall(expr_of_idxfunc func, _at, (List.map expr_of_intexpr (drop_last mylist))@[input]))])
    )
  |Idxfunc.FCompose l -> List.fold_right code_of_func l (input,[])
  | _ -> failwith("code_of_func, not handled: "^(Idxfunc.string_of_idxfunc func))        		
;;


let code_of_rstep (rstep_partitioned : rstep_partitioned) : code =
  let collect_children ((_, _, _, _, _, _, breakdowns ) : rstep_partitioned) : expr list =
    let res = ref IntSet.empty in  
    let g ((_,_,_,_,desc_cons,_):breakdown_enhanced) : _ =
      Spl.meta_iter_spl_on_spl (function
      | Spl.Construct(numchild, _, _, _) | Spl.ISumReinitConstruct(numchild, _, _, _, _, _, _) -> res := IntSet.add numchild !res
      | _ -> ()
      ) desc_cons;    
    in
    List.iter g breakdowns;
    List.map build_child_var (IntSet.elements !res)
  in

(*we should probably generate content while we are generating it instead of doing another pass*)
  let collect_freedoms ((_, _, _, _, _, _, breakdowns ) : rstep_partitioned) : expr list =
    let res = ref [] in  
    let g ((_,freedoms,_,_,_,_):breakdown_enhanced) : _ =
      res := (List.map (fun (l,_)->expr_of_intexpr l) freedoms) @ !res    
    in
    List.iter g breakdowns;
    !res  
  in


  let introduce_precomp : (Spl.spl -> Spl.spl) =
    Spl.meta_transform_spl_on_spl BottomUp (function
    | Spl.Diag(Idxfunc.Pre(f)) -> Spl.PreComp(Spl.Diag(Idxfunc.Pre(f)))
    | x -> x
    )
  in

  let cons_code_of_rstep ((_, _, _, _, _, _, breakdowns ) : rstep_partitioned) : code =
    let rec prepare_cons (e:Spl.spl) : code =
      let ne = Spl.simplify_spl(introduce_precomp (e)) in
      print_string ("cons code:"^(Spl.string_of_spl ne)^"\n"); 


      match ne with
      | Spl.Compose l -> simplify_code (Chain (List.map prepare_cons (List.rev l)))
      | Spl.Construct(numchild, rs, args, funcs) -> Assign(build_child_var(numchild), New(FunctionCall(rs, (List.map expr_of_intexpr (args))@(List.map (fun(x)->New(expr_of_idxfunc x)) funcs))))
      | Spl.ISumReinitConstruct(numchild, i, count, rs, cold, reinit, funcs) ->
	let child = build_child_var(numchild) in
	Chain([
	  ArrayAllocate(child, Ctype.Env(rs), (expr_of_intexpr count));
	  Loop(expr_of_intexpr i, expr_of_intexpr count, (
	    PlacementNew( 
	      (AddressOf(Nth(Cast(child, Ctype.Ptr(Ctype.Env(rs))), expr_of_intexpr i))),
	      (FunctionCall(rs, (List.map expr_of_intexpr (cold@reinit))@(List.map (fun(x)->New(expr_of_idxfunc x)) funcs))))
	  ))
	])
      | Spl.Diag Idxfunc.Pre(idxfunc) -> 
	(*FIXME this is wrong, we have to manage freaking GT loops, and that changes the size of the _dat.*)
	let var = gen_var#get Ctype.Int "t" in
	let (precomp, codelines) = code_of_func idxfunc (var,[]) in			    
	Chain([
	  ArrayAllocate(_dat, Ctype.Complex, expr_of_intexpr(Spl.spl_range(e)));
	  Loop(var, expr_of_intexpr(Spl.spl_range(e)),
	       Chain(codelines@[
		 Assign((Nth(Cast(_dat,Ctype.Ptr(Ctype.Complex)),var)),precomp)]))
				     ])
      | Spl.S _ | Spl.G _ | Spl.F _ -> Noop
      | Spl.BB spl -> prepare_cons spl
      (* | Spl.ISum(i, count, content) ->  *)
      (* 	(match (prepare_cons content) with  *)
      (* 	| Noop -> Noop (\*we do not want to produce empty isums, they may not be correct since the loop variable might be not cold*\) *)
      (* 	| (_ as c) -> Loop(expr_of_intexpr i, expr_of_intexpr count, c)) *)
      | Spl.GT(content,_,_,i)->
	failwith("FIXME : code me "^(Spl.string_of_spl ne))
      	(* (match (prepare_cons content) with *)
      	(* | Noop -> Noop (\*we do not want to produce empty isums, they may not be correct since the loop variable might be not cold*\) *)
      	(* | (_ as c) -> Loop(expr_of_intexpr i, expr_of_intexpr count, c)) *)
      | _ -> failwith("prepare_cons, not handled: "^(Spl.string_of_spl ne))
    in
    let rulecount = ref 0 in
    let g (stmt:code) ((condition,freedoms,_,_,desc_cons,_):breakdown_enhanced) : code  =
      let freedom_assigns = List.map (fun (l,r)->Assign(expr_of_intexpr l, expr_of_intexpr r)) freedoms in
      rulecount := !rulecount + 1;      
      If( Var(Ctype.Bool, Boolexpr.string_of_boolexpr condition), 
	 Chain( [Assign(_rule, expr_of_intexpr(Intexpr.IConstant !rulecount))] @ freedom_assigns @ [prepare_cons desc_cons]),
	 stmt)	
    in
    List.fold_left g (Error("no applicable rules")) breakdowns
  in

  let (name, _, cold, reinit, hot, funcs, _) = rstep_partitioned in 
  let cons_args = (List.map expr_of_intexpr ((IntExprSet.elements (cold))@(IntExprSet.elements (reinit))))@(List.map expr_of_idxfunc funcs) in
  let comp_args = _output::_input::List.map expr_of_intexpr (IntExprSet.elements hot) in
  
  let comp_code_of_rstep ((_, _, _, _, _, _, breakdowns ) : rstep_partitioned) (output:expr) (input:expr): code =
    let rec prepare_comp (output:expr) (input:expr) (e:Spl.spl): code =
      (* print_string ("comp code:"^(Spl.string_of_spl e)^"\n"); *)
      match e with
      | Spl.Compose l -> let ctype = Ctype.Complex in
			 let buffernames = 
			   let count = ref 0 in
			   let g (res:expr list) (_:Spl.spl) : expr list = 
			     count := !count + 1; 
			     (Var(Ctype.Ptr(ctype), "T"^(string_of_int !count))) :: res 
			   in
			   List.fold_left g [] (List.tl l) in
			 let out_in_spl = (List.combine (List.combine (buffernames @ [ output ]) (input :: buffernames)) (List.rev l)) in
			 let buffers = (List.combine (buffernames) (List.map Spl.spl_range (List.rev (List.tl l)))) in
			 Chain (
			   (List.map (fun (output,_)->(Declare output)) buffers)
			   @ (List.map (fun (output,size)->(ArrayAllocate(output,ctype,expr_of_intexpr(size)))) buffers)
			   @ (List.map (fun ((output,input),spl)->(prepare_comp output input spl)) out_in_spl)
			   @ (List.map (fun (output,size)->(ArrayDeallocate(output,expr_of_intexpr(size)))) buffers)
			 )
      | Spl.ISum(i, count, content) -> Loop(expr_of_intexpr i, expr_of_intexpr count, (prepare_comp output input content))
      | Spl.Compute(numchild, rs, hot,_,_) -> Ignore(MethodCall (Cast((build_child_var(numchild)),Ctype.Ptr(Ctype.Env(rs))), _compute, output::input::(List.map expr_of_intexpr hot)))
      | Spl.ISumReinitCompute(numchild, i, count, rs, hot,_,_) -> 
	Loop(expr_of_intexpr i, expr_of_intexpr count, Ignore(MethodCall(
	  (AddressOf(Nth(Cast(build_child_var(numchild), Ctype.Ptr(Ctype.Env(rs))), expr_of_intexpr i)))
	  , _compute, output::input::(List.map expr_of_intexpr hot))))
      | Spl.F 2 -> Chain([
	Assign ((Nth(output,(IConst 0))), (Plus (Nth(input, (IConst 0)), (Nth(input, (IConst 1))))));
	Assign ((Nth(output,(IConst 1))), (Minus (Nth(input, (IConst 0)), (Nth(input, (IConst 1))))))])
      | Spl.S idxfunc -> let var = gen_var#get Ctype.Int "t" in
			 let (index, codelines) = code_of_func idxfunc (var,[]) in			    
			     Loop(var, expr_of_intexpr(Spl.spl_domain(e)),
				  Chain(codelines@[Assign((Nth(output,index)), (Nth(input,var)))])) 
      | Spl.G idxfunc -> let var = gen_var#get Ctype.Int "t" in
			 let (index, codelines) = code_of_func idxfunc (var,[]) in			    
			     Loop(var, expr_of_intexpr(Spl.spl_range(e)),
				  Chain(codelines@[Assign((Nth(output,var)), (Nth(input,index)))])) 
      | Spl.Diag Idxfunc.Pre Idxfunc.FArg (_, l) -> 
	let var = gen_var#get Ctype.Int "t" in
	let rec f = function
	  | _::[] -> var
	  | a::b::[] -> Plus(Mul(expr_of_intexpr a,expr_of_intexpr b), var)
	  | _ -> failwith("FArg not handled")
	in
	Loop(var, expr_of_intexpr(Spl.spl_range(e)),
	     Chain([Assign((Nth(output,var)), Mul(Nth(input,var),Nth(Cast(_dat,Ctype.Ptr(Ctype.Complex)), (f l))))]))
      | Spl.GT(a, g, s, v::[]) ->  
      	let i = Intexpr.gen_loop_counter#get () in
	let spl = Spl.ISum(i, v, Spl.Compose([Spl.S(Idxfunc.FDown(s, i, 0));Spl.Down(a, i, 0);Spl.G(Idxfunc.FDown(g, i, 0))])) in
	(prepare_comp output input (Spl.simplify_spl spl))
      | Spl.BB spl -> (* Compiler.compile_bloc *) (prepare_comp output input spl) (*FIXME re-enable compile*)
      | _ -> failwith("prepare_comp, not handled: "^(Spl.string_of_spl e))
    in
    let rulecount = ref 0 in
    let g (stmt:code) ((_,_,_,_,_,desc_comp):breakdown_enhanced) : code  =
      rulecount := !rulecount + 1;
      If(Equal(_rule, expr_of_intexpr(Intexpr.IConstant !rulecount)),
	 prepare_comp output input desc_comp, 
	 stmt)
	
    in
    List.fold_left g (Error("internal error: no valid rule has been selected")) breakdowns
  in

  print_string ("=== Building "^name^" ===\n");
  let met = Method(Ctype.Void, _compute, comp_args, comp_code_of_rstep rstep_partitioned _output _input) in
  print_string ("... built method \n");
  let cons = Constructor(cons_args, cons_code_of_rstep rstep_partitioned) in
  print_string ("... built constructor \n");
  let claz = Class (name, _rs, _rule::_dat::cons_args@(collect_children rstep_partitioned) @ (collect_freedoms rstep_partitioned), [cons;met]) in
  print_string ("... built class \n");
  claz
;;

let code_of_envfunc ((name, f, args, fargs) : envfunc) : code =
  print_string ("=== Building "^name^" ===\n");
  print_string ("definition:"^(Idxfunc.string_of_idxfunc f)^"\n");
  print_string ("args:"^(String.concat ", " (List.map Intexpr.string_of_intexpr args))^"\n");
  print_string ("fargs:"^(String.concat ", " (List.map Idxfunc.string_of_idxfunc fargs))^"\n");

  let g = ref f in 
  let rankvars = ref [] in
  while (Idxfunc.rank_of_func !g > 0) do
    print_string ("processing:"^(Idxfunc.string_of_idxfunc !g)^"\n");    
    let i = Intexpr.gen_loop_counter#get () in 
    g := Idxfunc.simplify_idxfunc (Idxfunc.FDown(!g, i, 0));
    rankvars := (expr_of_intexpr i)::!rankvars;
  done;
  let input = gen_var#get Ctype.Int "t" in
  let(output, code) = (code_of_func !g (input,[])) in
  let cons_args = (List.map expr_of_intexpr args)@(List.map expr_of_idxfunc fargs) in
  Class(name, (Idxfunc.ctype_of_func f), cons_args, [
    Constructor(cons_args, Noop);
    Method(Ctype.Complex, _at, !rankvars @ [input], Chain(code@[Return(output)]))])
;;

let code_of_lib ((funcs,rsteps) : lib) : code list =
  (List.map code_of_envfunc funcs)@(List.map code_of_rstep rsteps)
;;

