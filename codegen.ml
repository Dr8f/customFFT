open Util
;;

open Lib
;;

open Code
;;


let _rs = "RS"
;;

let _func = "func"
;;

let _at = "at"
;;

let _compute = "compute"
;;

let _rule = Var(Int, "_rule")
;;

let _dat = Var(Ptr(Complex), "_dat")
;;

let build_child_var (num:int) : expr =
  Var(Ptr(Env(_rs)),"child"^(string_of_int num))
;;

let expr_of_intexpr (intexpr : Spl.intexpr) : expr =
  match intexpr with
    Spl.IConstant x -> IConst x
  | x -> Var(Int, Spl.string_of_intexpr intexpr)
;;

let _output = Var(Ptr(Complex),"Y")
;;

let _input = Var(Ptr(Complex),"X")
;;


let rec expr_of_idxfunc (idxfunc : Spl.idxfunc) : expr =
  match idxfunc with
  | Spl.FArg(n, _) -> Var(Func, n)
  | Spl.PreWrap(n, l, funcs, _) -> FunctionCall(n, ((List.map expr_of_intexpr l)@(List.map expr_of_idxfunc funcs)))
;;


let rec code_of_func (func : Spl.idxfunc) ((input,code):expr * code list) : expr * code list =
  match func with
  |Spl.FH(_,_,b,s) -> let output = gen_var#get Int "t" in
		      (output,code@[Declare(output);Assign(output, Plus((expr_of_intexpr b), Mul((expr_of_intexpr s),input)))])
  |Spl.FD(n,k) -> let output = gen_var#get Complex "c" in
		  (output,code@[Declare(output);Assign(output, FunctionCall("omega", [(expr_of_intexpr n);UniMinus(Mul(Mod(input,(expr_of_intexpr k)), Divide(input,(expr_of_intexpr k))))]))])
  |Spl.FArg(_,_) -> let output = gen_var#get Complex "c" in
		    (output,code@[Declare(output);Assign(output, MethodCall(expr_of_idxfunc func, _at, [input]))])  
  |Spl.FCompose l -> List.fold_right code_of_func l (input,[])
;;


let code_of_rstep (rstep_partitioned : rstep_partitioned) : code =
  let collect_children ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) : expr list =
    let res = ref IntSet.empty in  
    let g ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : _ =
      Spl.meta_iter_spl_on_spl (function
      | Spl.Construct(numchild, _, _, _) | Spl.ISumReinitConstruct(numchild, _, _, _, _, _, _) -> res := IntSet.add numchild !res
      | _ -> ()
      ) desc_cons;    
    in
    List.iter g breakdowns;
    List.map build_child_var (IntSet.elements !res)
  in

(*we should probably generate content while we are generating it instead of doing another pass*)
  let collect_freedoms ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) : expr list =
    let res = ref [] in  
    let g ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : _ =
      res := (List.map (fun (l,r)->expr_of_intexpr l) freedoms) @ !res    
    in
    List.iter g breakdowns;
    !res  
  in

  let cons_code_of_rstep ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) : code =
    let rec prepare_cons (e:Spl.spl) : code =
      (* print_string ("BOOM:"^(Spl.string_of_spl e)^"\n"); *)
      match e with
      | Spl.Compose l -> Chain (List.map prepare_cons (List.rev l)) 
      | Spl.Construct(numchild, rs, args, funcs) -> Assign(build_child_var(numchild), New(FunctionCall(rs, (List.map expr_of_intexpr (args))@(List.map (fun(x)->New(expr_of_idxfunc x)) funcs))))
      | Spl.ISumReinitConstruct(numchild, i, count, rs, cold, reinit, funcs) ->
	let child = build_child_var(numchild) in
	Chain([
	  ArrayAllocate(child, Env(rs), (expr_of_intexpr count));
	  Loop(expr_of_intexpr i, expr_of_intexpr count, (
	    PlacementNew( 
	      (AddressOf(Nth(Cast(child, Ptr(Env(rs))), expr_of_intexpr i))),
	      (FunctionCall(rs, (List.map expr_of_intexpr (cold@reinit))@(List.map (fun(x)->New(expr_of_idxfunc x)) funcs))))
	  ))
	])
      | Spl.Diag Spl.Pre(idxfunc) -> let var = gen_var#get Int "t" in
				     let (precomp, codelines) = code_of_func idxfunc (var,[]) in			    
				     Chain([
				       ArrayAllocate(_dat, Complex, expr_of_intexpr(Spl.range(e)));
				       Loop(var, expr_of_intexpr(Spl.range(e)),
					    Chain(codelines@[
					      Assign((Nth(Cast(_dat,Ptr(Complex)),var)),precomp)]))
				     ])
      | Spl.S _ | Spl.G _ | Spl.F _ -> Chain([])
      | Spl.BB spl -> prepare_cons spl

    in
    let rulecount = ref 0 in
    let g (stmt:code) ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : code  =
      let freedom_assigns = List.map (fun (l,r)->Assign(expr_of_intexpr l, expr_of_intexpr r)) freedoms in
      rulecount := !rulecount + 1;      
      If( Var(Bool, Spl.string_of_boolexpr condition), 
	 Chain( [Assign(_rule, expr_of_intexpr(Spl.IConstant !rulecount))] @ freedom_assigns @ [prepare_cons desc_cons]),
	 stmt)	
    in
    print_string "===== Building an rstep constructor =====\n";
    List.fold_left g (Error("no applicable rules")) breakdowns
  in

  let comp_code_of_rstep ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) (output:expr) (input:expr): code =
    let rec prepare_comp (output:expr) (input:expr) (e:Spl.spl): code =
      match e with
      | Spl.Compose l -> let ctype = Complex in
			 let buffernames = 
			   let count = ref 0 in
			   let g (res:expr list) (_:Spl.spl) : expr list = 
			     count := !count + 1; 
			     (Var(Ptr(ctype), "T"^(string_of_int !count))) :: res 
			   in
			   List.fold_left g [] (List.tl l) in
			 let out_in_spl = (List.combine (List.combine (buffernames @ [ output ]) (input :: buffernames)) (List.rev l)) in
			 let buffers = (List.combine (buffernames) (List.map Spl.range (List.rev (List.tl l)))) in
			 Chain (
			   (List.map (fun (output,size)->(Declare output)) buffers)
			   @ (List.map (fun (output,size)->(ArrayAllocate(output,ctype,expr_of_intexpr(size)))) buffers)
			   @ (List.map (fun ((output,input),spl)->(prepare_comp output input spl)) out_in_spl)
			   @ (List.map (fun (output,size)->(ArrayDeallocate(output,expr_of_intexpr(size)))) buffers)
			 )
      | Spl.ISum(i, count, content) -> Loop(expr_of_intexpr i, expr_of_intexpr count, (prepare_comp output input content))
      | Spl.Compute(numchild, rs, hot,_,_) -> Ignore(MethodCall (Cast((build_child_var(numchild)),Ptr(Env(rs))), _compute, output::input::(List.map expr_of_intexpr hot)))
      | Spl.ISumReinitCompute(numchild, i, count, rs, hot,_,_) -> 
	Loop(expr_of_intexpr i, expr_of_intexpr count, Ignore(MethodCall(
	  (AddressOf(Nth(Cast(build_child_var(numchild), Ptr(Env(rs))), expr_of_intexpr i)))
	  , _compute, output::input::(List.map expr_of_intexpr hot))))
      | Spl.F 2 -> Chain([
	Assign ((Nth(output,(IConst 0))), (Plus (Nth(input, (IConst 0)), (Nth(input, (IConst 1))))));
	Assign ((Nth(output,(IConst 1))), (Minus (Nth(input, (IConst 0)), (Nth(input, (IConst 1))))))])
      | Spl.S idxfunc -> let var = gen_var#get Int "t" in
			 let (index, codelines) = code_of_func idxfunc (var,[]) in			    
			     Loop(var, expr_of_intexpr(Spl.domain(e)),
				  Chain(codelines@[Assign((Nth(output,index)), (Nth(input,var)))])) 
      | Spl.G idxfunc -> let var = gen_var#get Int "t" in
			 let (index, codelines) = code_of_func idxfunc (var,[]) in			    
			     Loop(var, expr_of_intexpr(Spl.range(e)),
				  Chain(codelines@[Assign((Nth(output,var)), (Nth(input,index)))])) 
      | Spl.Diag _ -> let var = gen_var#get Int "t" in
		      Loop(var, expr_of_intexpr(Spl.range(e)),
			   Chain([Assign((Nth(output,var)), Mul(Nth(input,var),Nth(Cast(_dat,Ptr(Complex)),var)))]))
      | Spl.BB spl -> Compiler.compile_bloc(prepare_comp output input spl)
    in
    let rulecount = ref 0 in
    let g (stmt:code) ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : code  =
      rulecount := !rulecount + 1;
      If(Equal(_rule, expr_of_intexpr(Spl.IConstant !rulecount)),
	 prepare_comp output input desc_comp, 
	 stmt)
	
    in
    print_string "===== Building an rstep content =====\n";
    List.fold_left g (Error("internal error: no valid rule has been selected")) breakdowns
  in

  let (name, rstep, cold, reinit, hot, funcs, breakdowns) = rstep_partitioned in 
  let cons_args = (List.map expr_of_intexpr ((IntExprSet.elements (cold))@(IntExprSet.elements (reinit))))@(List.map expr_of_idxfunc funcs) in
  print_string ("=== Building "^name^" ===\n");
  Class (name, _rs, _rule::_dat::cons_args@(collect_children rstep_partitioned) @ (collect_freedoms rstep_partitioned), [
    Constructor(cons_args, cons_code_of_rstep rstep_partitioned);	       
    Method(Void, _compute, _output::_input::List.map expr_of_intexpr (IntExprSet.elements hot), comp_code_of_rstep rstep_partitioned _output _input)])
;;

let code_of_envfunc ((name, f, args, fargs) : envfunc) : code =  
  let input = gen_var#get Int "t" in
  let(output, code) = (code_of_func f (input,[])) in
  let cons_args = (List.map expr_of_intexpr args)@(List.map expr_of_idxfunc fargs) in
  print_string ("=== Building "^name^" ===\n");
  Class(name, _func, cons_args, [
    Constructor(cons_args, Noop);
    Method(Complex, _at, [input], Chain(code@[Return(output)]))])
;;

let code_of_lib ((funcs,rsteps) : lib) : code list =
  (List.map code_of_envfunc funcs)@(List.map code_of_rstep rsteps)
;;

