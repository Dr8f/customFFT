open Lib
;;

type ctype = 
  Int
| Env
;;

type var = 
|Var of ctype * string
;;

type intrvalue = 
  ContentsOf of var
| ValueOf of Spl.intexpr
;;

type envrvalue = 
Create of string * intrvalue list
;;

type code =
  Class of string(*name*) * var list(*cold args*) * code (*cons*)
| Chain of code list
| Noop
| Error of string
| IntAssign of var * intrvalue 
| EnvAssign of var * envrvalue
| If of Spl.boolexpr * code * code
| Loop of var * intrvalue * code
;;

let cons_code_of_rstep_partitioned ((name, rstep, cold, reinit, hot, breakdowns ) : rstep_partitioned) =
  let envcount = ref 0 in
  let prepare_env_cons (rs:string) (cold:Spl.intexpr list) (reinit:Spl.intexpr list) : code =
    envcount := !envcount + 1;
    EnvAssign (Var(Env, "child"^string_of_int !envcount),Create(rs, List.map (fun(x)->ContentsOf(Var(Int,Spl.string_of_intexpr x))) (List.append cold reinit)))
  in

  let rec prepare_cons (e:Spl.spl) : code =
    match e with
    |Spl.Compose l -> Chain (List.map prepare_cons (List.rev l)) 
    |Spl.ISum(i,count,spl) -> Loop(Var(Int, Spl.string_of_intexpr i), ValueOf count,(prepare_cons spl)) (*FIXME, there's some hoisting*)
    |Spl.PartitionnedCall(callee,cold,reinit,_) ->  prepare_env_cons callee cold reinit 
    | _ -> Error("UNIMPLEMENTED")
  in
  let rulecount = ref 0 in
  let g (stmt:code) ((condition,freedoms,desc,desc_with_calls):breakdown) : code  =
    let freedom_assigns = List.map (fun (l,r)->IntAssign(Var(Int,Spl.string_of_intexpr l), ContentsOf(Var(Int,Spl.string_of_intexpr r)))) freedoms in
    rulecount := !rulecount + 1;
    
    If(condition, 
       Chain( [IntAssign(Var(Int, "_rule"), ValueOf(Spl.IConstant !rulecount))] @ freedom_assigns @ [prepare_cons desc_with_calls]), 
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

