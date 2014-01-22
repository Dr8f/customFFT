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
;;

type expr = 
| Var of ctype * string
| Nth of expr * expr
| Cast of expr * ctype
| Equal of expr * expr
| IntexprValueOf of Spl.intexpr
| BoolValueOf of Spl.boolexpr
| IdxfuncValueOf of Spl.idxfunc
| CreateEnv of string * expr list
| New of expr
| MethodCall of expr (*object*) * string (*method name*) * expr list (*arguments*)
| Mul of expr * expr
| Plus of expr * expr
| Minus of expr
| Mod of expr * expr
| Divide of expr * expr
| Omega of expr * expr
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
| Loop of Spl.intexpr (*loop variable*) * expr (*count*) * code 
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
  IntexprValueOf intexpr
;;


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
;;

(*we should probably generate content while we are generating it instead of doing another pass*)
let collect_freedoms ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) : expr list =
  let res = ref [] in  
  let g ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : _ =
    res := (List.map (fun (l,r)->IntexprValueOf l) freedoms) @ !res    
  in
  List.iter g breakdowns;
  !res  
;;

let cons_code_of_rstep_partitioned ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) : code =
  let rec prepare_cons (e:Spl.spl) : code =
    match e with
    | Spl.Compose l -> Chain (List.map prepare_cons (List.rev l)) 
    | Spl.Construct(numchild, rs, args) -> Assign(build_child_var(numchild), New(CreateEnv(rs, List.map expr_of_intexpr args)))
    | Spl.ISumReinitConstruct(numchild, i, count, rs, cold, reinit, funcs) ->
      let child = build_child_var(numchild) in
      Chain([
	ArrayAllocate(child, Env(rs), (IntexprValueOf count));
	Loop(i, IntexprValueOf count, (
	  PlacementNew( 
	    (Nth(Cast(child, Ptr(Env(rs))), IntexprValueOf i)), 
	    (CreateEnv(rs, (List.map expr_of_intexpr (cold@reinit))@(List.map (fun(x)->New(IdxfuncValueOf x)) funcs))))
	))
      ])	
    | _ -> Error("UNIMPLEMENTED")
  in
  let rulecount = ref 0 in
  let g (stmt:code) ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : code  =
    let freedom_assigns = List.map (fun (l,r)->Assign(IntexprValueOf l, IntexprValueOf r)) freedoms in
    rulecount := !rulecount + 1;
    
    If((BoolValueOf condition), 
       Chain( [Assign(_rule, IntexprValueOf(Spl.IConstant !rulecount))] @ freedom_assigns @ [prepare_cons desc_cons]), 
       Error("no applicable rules"))
      
  in
  List.fold_left g (Error("no error")) breakdowns
;;


let comp_code_of_rstep_partitioned ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) (output:expr) (input:expr): code =
  let prepare_env_comp (ctype:ctype) (expr:expr) (rs:string) (args:Spl.intexpr list) (output:expr) (input:expr): code =
    Ignore(MethodCall (Cast(expr,Ptr(ctype)), _compute, output::input::(List.map expr_of_intexpr args)))    
  in

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
			 @ (List.map (fun (output,size)->(ArrayAllocate(output,ctype,IntexprValueOf(size)))) buffers)
			 @ (List.map (fun ((output,input),spl)->(prepare_comp output input spl)) out_in_spl)
			 @ (List.map (fun (output,size)->(ArrayDeallocate(output,IntexprValueOf(size)))) buffers)
		       )
    | Spl.ISum(i, count, content) -> Loop(i, IntexprValueOf count, (prepare_comp output input content))
    | Spl.Compute(numchild, rs, hot,_,_) -> prepare_env_comp (Env(rs)) (build_child_var(numchild)) rs hot output input
    | Spl.ISumReinitCompute(numchild, i, count, rs, hot,_,_) -> 
      Loop(i, IntexprValueOf count, (prepare_env_comp (Env(rs)) (Nth(build_child_var(numchild), IntexprValueOf(i))) rs hot output input))
    | _ -> Error("UNIMPLEMENTED")
  in
  let rulecount = ref 0 in
  let g (stmt:code) ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : code  =
    let freedom_assigns = List.map (fun (l,r)->Assign(IntexprValueOf l, IntexprValueOf r)) freedoms in
    rulecount := !rulecount + 1;
    
    If(Equal(_rule, IntexprValueOf(Spl.IConstant !rulecount)),
       prepare_comp output input desc_comp, 
       Error("internal error: no valid rule has been selected"))
      
  in
  List.fold_left g (Error("no error")) breakdowns
;;


let code_of_lib ((funcs,rsteps) : lib) : code = 
  let code_of_func ((name, f, args, fargs) : envfunc) : code = 
    let count = ref 0 in
    let vargen (ctype:ctype) : expr = 
      count := !count + 1;
      Var(ctype, "t"^(string_of_int (!count)))
    in
    
    let code_of_at (f : Spl.idxfunc) (input : expr) : code =
      let g (func : Spl.idxfunc) ((input,code):expr * code list) : expr * code list =
	match func with
	|Spl.FH(_,_,b,s) -> let output = vargen(Int) in
			    (output,code@[Declare(output);Assign(output, Plus((IntexprValueOf b), Mul((IntexprValueOf s),input)))])
	|Spl.FD(n,k) ->  let output = vargen(Complex) in
			 (output,code@[Declare(output);Assign(output, Omega((IntexprValueOf n), Minus(Mul(Mod(input,(IntexprValueOf k)), Divide(input,(IntexprValueOf k))))))])
	|Spl.FArg(name,_) -> let output = vargen(Complex) in
			     (output,code@[Declare(output);Assign(output, MethodCall(IdxfuncValueOf func, _at, [input]))])  
      in
      match f with
      |Spl.FCompose l -> let(output,code) = List.fold_right g l (input,[]) in
			 Chain(code@[Return(output)])
    in

    let input = vargen(Int) in
    let code = (code_of_at f input) in
    let cons_args = (List.map expr_of_intexpr args)@(List.map (function x -> IdxfuncValueOf x) fargs) in
    Class(name,
	  _func,
	  cons_args,
	  [
	    Constructor(
	      cons_args,
	      Noop
	    );
	    Method(
	      Complex,
	      _at,
	      [input], 
	      code
	    )
	  ]	    
    )
  in
  let code_of_rstep (rstep_partitioned : rstep_partitioned) : code =
    let (name, rstep, cold, reinit, hot, funcs, breakdowns) = rstep_partitioned in 
    let output = Var(Ptr(Complex),"Y") in
    let input = Var(Ptr(Complex),"X") in
    let cons_args = (List.map expr_of_intexpr ((IntExprSet.elements (cold))@(IntExprSet.elements (reinit))))@(List.map (function x -> IdxfuncValueOf x) funcs) in
    Class (name,
	   _rs,
	   _rule::_dat::cons_args@(collect_children rstep_partitioned) @ (collect_freedoms rstep_partitioned),
	   [
	     Constructor(
	       cons_args,
	       cons_code_of_rstep_partitioned rstep_partitioned
	     );	       
	     Method(
	       Void,
	       _compute,
	       output::input::List.map expr_of_intexpr (IntExprSet.elements hot),
	       comp_code_of_rstep_partitioned rstep_partitioned output input
	     )
	   ]
    )
  in
  Chain ((List.map code_of_func funcs)@(List.map code_of_rstep rsteps))
;;

