open Lib
;;

type ctype = 
  Int
;;

type var = 
|Var of ctype * string
;;

type code =
  Class of string(*name*) * var list(*cold args*) * code (*cons*)
| Chain of code list
| Noop
| Error of string
| Assign of var * var (* FIXME : should be lvalue and rvalue *)
| If of Spl.boolexpr * code * code
;;

let cons_code_of_rstep_partitioned ((name, rstep, cold, reinit, hot, breakdowns ) : rstep_partitioned) = 
  let rulecount = ref 0 in
  let g (stmt:code) ((condition,freedoms,desc,desc_with_calls):breakdown) : code  =
    let freedom_assigns = List.map (fun (l,r)->Assign(Var(Int,Spl.string_of_intexpr l), Var(Int,Spl.string_of_intexpr r))) freedoms in
    rulecount := !rulecount + 1;
    
    If(condition, 
       Chain( [Assign(Var(Int, "_rule"), Var(Int, "FIXME: IConstant !rulecount"))] @ freedom_assigns ), (* @ [prepare_cons desc_with_calls] *)
       Error("no applicable rules"))
      
  in
  List.fold_left g (Error("no error")) breakdowns
;;

let code_of_lib (lib : lib) : code = 
  let f (rstep_partitioned : rstep_partitioned) =
    let (name, rstep, cold, reinit, hot, breakdowns) = rstep_partitioned in 
    Class (name
	     , List.map (function x -> Var(Int, Spl.string_of_intexpr x)) (IntExprSet.elements cold)
	       , cons_code_of_rstep_partitioned rstep_partitioned		 
    )
  in
  Chain (List.map f lib)
;;

