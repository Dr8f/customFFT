open Lib
;;

type ctype = 
  Int
| Env of string
| Func
| Ptr of ctype
| Char
| Complex
| Void
| Bool
;;

type expr = 
| Var of ctype * string
| Nth of expr * expr
| Cast of expr * ctype
| Equal of expr * expr
| New of expr
| Mul of expr * expr
| Plus of expr * expr
| Minus of expr
| Mod of expr * expr
| Divide of expr * expr
| FunctionCall of string (*functionname*) * expr list (*arguments*)
| MethodCall of expr (*object*) * string (*method name*) * expr list (*arguments*)
;;

type cmethod = 
  Constructor of expr list(*args*) * code 
| Method of ctype (*return type*) * string (* functionname *) * expr list(* args*)  * code
and
code =
  Class of string(*class name*) * string (*class template from which it is derived*) * expr list (*member variables*) * cmethod list (*methods*)
| Chain of code list
| Noop
| Error of string
| Assign of expr(*dest*) * expr (*origin*)
| ArrayAllocate of expr (*pointer*) * ctype (*element type*) * expr (*element count*)
| PlacementNew of expr (*address*) * expr (*content*)
| If of expr (*condition*) * code (*true branch*) * code (*false branch*)
| Loop of expr (*loop variable*) * expr (*count*) * code 
| ArrayDeallocate of expr (*pointer*) * expr (*element count*)
| Return of expr
| Declare of expr
| Ignore of expr (*expression with side effect*)
;; 

(* let meta_collect_code_on_code (f : code -> 'a list) : (code -> 'a list) = *)
(*   let z (g : code -> 'a list) (e : code) : 'a list = *)
(*     match e with *)
(*     | Class(_,_,_,_,cons,comp,_,_,_,_) -> (g cons) @ (g comp) *)
(*     | Chain l -> List.flatten (List.map g l) *)
(*     | If(_,a,b) -> (g a)@(g b) *)
(*     | Loop(_,_,c) -> g c *)
(*     | _ -> [] *)
(*   in *)
(*   Spl.recursion_collect f z *)
(* ;; *)

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

let _dat = Var(Ptr(Char), "_dat")
;;

let build_child_var (num:int) : expr =
  Var(Ptr(Env(_rs)),"child"^(string_of_int num))
;;

let expr_of_intexpr (intexpr : Spl.intexpr) : expr =
  Var(Int, Spl.string_of_intexpr intexpr)
;;

let expr_of_idxfunc (idxfunc : Spl.idxfunc) : expr =
  Var(Func, Spl.string_of_idxfunc idxfunc)
;;

let _output = Var(Ptr(Complex),"Y")
;;

let _input = Var(Ptr(Complex),"X")
;;

let code_of_rstep (rstep_partitioned : rstep_partitioned) : code =
(*we should probably generate content while we are generating it instead of doing another pass*)
  let collect_children ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) : expr list =
    let res = ref [] in  
    let g ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : _ =
      Spl.meta_iter_spl_on_spl (function
      | Spl.Construct(numchild, _, _) | Spl.ISumReinitConstruct(numchild, _, _, _, _, _, _) -> res := (build_child_var numchild)::!res 
      | _ -> ()
      ) desc_cons;    
    in
    List.iter g breakdowns;
    !res
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
      match e with
      | Spl.Compose l -> Chain (List.map prepare_cons (List.rev l)) 
      | Spl.Construct(numchild, rs, args) -> Assign(build_child_var(numchild), New(FunctionCall(rs, List.map expr_of_intexpr args)))
      | Spl.ISumReinitConstruct(numchild, i, count, rs, cold, reinit, funcs) ->
	let child = build_child_var(numchild) in
	Chain([
	  ArrayAllocate(child, Env(rs), (expr_of_intexpr count));
	  Loop(expr_of_intexpr i, expr_of_intexpr count, (
	    PlacementNew( 
	      (Nth(Cast(child, Ptr(Env(rs))), expr_of_intexpr i)), 
	      (FunctionCall(rs, (List.map expr_of_intexpr (cold@reinit))@(List.map (fun(x)->New(expr_of_idxfunc x)) funcs))))
	  ))
	])	
    in
    let rulecount = ref 0 in
    let g (stmt:code) ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : code  =
      let freedom_assigns = List.map (fun (l,r)->Assign(expr_of_intexpr l, expr_of_intexpr r)) freedoms in
      rulecount := !rulecount + 1;      
      If( Var(Bool, Spl.string_of_boolexpr condition), 
	 Chain( [Assign(_rule, expr_of_intexpr(Spl.IConstant !rulecount))] @ freedom_assigns @ [prepare_cons desc_cons]),
	 stmt)	
    in
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
	Loop(expr_of_intexpr i, expr_of_intexpr count, Ignore(MethodCall(Cast((Nth(build_child_var(numchild), expr_of_intexpr(i))),Ptr(Env(rs))), _compute, output::input::(List.map expr_of_intexpr hot))))
      | _ -> Error("UNIMPLEMENTED")
    in
    let rulecount = ref 0 in
    let g (stmt:code) ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : code  =
      let freedom_assigns = List.map (fun (l,r)->Assign(expr_of_intexpr l, expr_of_intexpr r)) freedoms in
      rulecount := !rulecount + 1;
      
      If(Equal(_rule, expr_of_intexpr(Spl.IConstant !rulecount)),
	 prepare_comp output input desc_comp, 
	 stmt)
	
    in
    List.fold_left g (Error("internal error: no valid rule has been selected")) breakdowns
  in

  let (name, rstep, cold, reinit, hot, funcs, breakdowns) = rstep_partitioned in 
  let cons_args = (List.map expr_of_intexpr ((IntExprSet.elements (cold))@(IntExprSet.elements (reinit))))@(List.map expr_of_idxfunc funcs) in
  Class (name, _rs, _rule::_dat::cons_args@(collect_children rstep_partitioned) @ (collect_freedoms rstep_partitioned), [
    Constructor(cons_args, cons_code_of_rstep rstep_partitioned);	       
    Method(Void, _compute, _output::_input::List.map expr_of_intexpr (IntExprSet.elements hot), comp_code_of_rstep rstep_partitioned _output _input)])
;;

let code_of_envfunc ((name, f, args, fargs) : envfunc) : code = 
  let count = ref 0 in
  let vargen (ctype:ctype) : expr = 
    count := !count + 1;
    Var(ctype, "t"^(string_of_int (!count)))
  in
  
  let rec code_of_func (func : Spl.idxfunc) ((input,code):expr * code list) : expr * code list =
    match func with
    |Spl.FH(_,_,b,s) -> let output = vargen(Int) in
			(output,code@[Declare(output);Assign(output, Plus((expr_of_intexpr b), Mul((expr_of_intexpr s),input)))])
    |Spl.FD(n,k) -> let output = vargen(Complex) in
		    (output,code@[Declare(output);Assign(output, FunctionCall("omega", [(expr_of_intexpr n);Minus(Mul(Mod(input,(expr_of_intexpr k)), Divide(input,(expr_of_intexpr k))))]))])
    |Spl.FArg(_,_) -> let output = vargen(Complex) in
		      (output,code@[Declare(output);Assign(output, MethodCall(expr_of_idxfunc func, _at, [input]))])  
    |Spl.FCompose l -> List.fold_right code_of_func l (input,[])
  in
  
  let input = vargen(Int) in
  let(output, code) = (code_of_func f (input,[])) in
  let cons_args = (List.map expr_of_intexpr args)@(List.map expr_of_idxfunc fargs) in
  Class(name, _func, cons_args, [
    Constructor(cons_args, Noop);
    Method(Complex, _at, [input], Chain(code@[Return(output)]))])
;;

let code_of_lib ((funcs,rsteps) : lib) : code = 
  Chain ((List.map code_of_envfunc funcs)@(List.map code_of_rstep rsteps))
;;

