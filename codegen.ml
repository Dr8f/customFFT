open Lib
;;

type ctype = 
  Int
| Env of string
;;

type var = 
|Var of ctype * string
;;

type intrvalue = 
  ContentsOf of var
| ValueOf of Spl.intexpr
;;

type boolrvalue = 
  Equal of intrvalue * intrvalue
| BoolValueOf of Spl.boolexpr
;;

type envrvalue = 
CreateEnv of string * intrvalue list
;;

type envlvalue = 
  Into of var
| Nth of var * intrvalue
;;

type code =
  Class of string(*name*) * var list(*cold args*) * var list(*reinit args*) * var list(*hot args*) * code (*cons*) * code (*comp*) * string (*output*) * string (*input*)
| Chain of code list
| Noop
| Error of string
| IntAssign of var * intrvalue 
| EnvAssign of envlvalue * envrvalue
| EnvArrayAllocate of string * string * intrvalue
| MethodCall of envlvalue * string * intrvalue list * string * string
| If of boolrvalue * code * code
| Loop of var * intrvalue * code
;;

let cons_code_of_rstep_partitioned ((name, rstep, cold, reinit, hot, breakdowns ) : rstep_partitioned) : code =
  let prepare_env_cons (envlvalue:envlvalue) (rs:string) (args:Spl.intexpr list) : code =
    EnvAssign (envlvalue, CreateEnv(rs, List.map (fun(x)->ContentsOf(Var(Int,Spl.string_of_intexpr x))) args))
  in

  let rec prepare_cons (e:Spl.spl) : code =
    match e with
    | Spl.Compose l -> Chain (List.map prepare_cons (List.rev l)) 
    | Spl.Construct(numchild, rs, cold) -> prepare_env_cons (Into(Var(Env(rs), "child"^(string_of_int numchild)))) rs cold
    | Spl.ISumReinitConstruct(numchild, i, count, rs, cold, reinit) ->
      let name = "child"^(string_of_int numchild) in
      let loopvar = Var(Int, Spl.string_of_intexpr i) in 
      Chain([
	EnvArrayAllocate(name, rs, (ValueOf count));
	Loop(loopvar, ValueOf count, (prepare_env_cons (Nth(Var(Env(rs), name), (ContentsOf(loopvar)))) rs (cold@reinit))) 
      ])
    | _ -> Error("UNIMPLEMENTED")
  in
  let rulecount = ref 0 in
  let g (stmt:code) ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : code  =
    let freedom_assigns = List.map (fun (l,r)->IntAssign(Var(Int,Spl.string_of_intexpr l), ContentsOf(Var(Int,Spl.string_of_intexpr r)))) freedoms in
    rulecount := !rulecount + 1;
    
    If((BoolValueOf condition), 
       Chain( [IntAssign(Var(Int, "_rule"), ValueOf(Spl.IConstant !rulecount))] @ freedom_assigns @ [prepare_cons desc_cons]), 
       Error("no applicable rules"))
      
  in
  List.fold_left g (Error("no error")) breakdowns
;;

let comp_code_of_rstep_partitioned ((name, rstep, cold, reinit, hot, breakdowns ) : rstep_partitioned) (output:string) (input:string): code =
  let prepare_env_comp (envlvalue:envlvalue) (rs:string) (args:Spl.intexpr list) (output:string) (input:string): code =
    MethodCall (envlvalue, "compute", (List.map (fun(x)->ContentsOf(Var(Int,Spl.string_of_intexpr x))) args), output, input)
  in

  let rec prepare_comp (output:string) (input:string) (e:Spl.spl): code =
    match e with
    | Spl.Compose l -> Chain (List.map (fun (x)->(prepare_comp output input x)) (List.rev l)) (*FIXME*)
    | Spl.ISum(i, count, content) -> Loop(Var(Int, Spl.string_of_intexpr i), ValueOf count, (prepare_comp output input content))
    | Spl.Compute(numchild, rs, hot) -> prepare_env_comp (Into(Var(Env(rs), "child"^(string_of_int numchild)))) rs hot output input
    | Spl.ISumReinitCompute(numchild, i, count, rs, hot) -> 
      let loopvar = Var(Int, Spl.string_of_intexpr i) in
      Loop(loopvar, ValueOf count, (prepare_env_comp (Nth(Var(Env(rs), "child"^(string_of_int numchild)), (ContentsOf(loopvar)))) rs hot output input))
    | _ -> Error("UNIMPLEMENTED")
  in
  let rulecount = ref 0 in
  let g (stmt:code) ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : code  =
    let freedom_assigns = List.map (fun (l,r)->IntAssign(Var(Int,Spl.string_of_intexpr l), ContentsOf(Var(Int,Spl.string_of_intexpr r)))) freedoms in
    rulecount := !rulecount + 1;
    
    If(Equal(ContentsOf(Var(Int, "_rule")), ValueOf(Spl.IConstant !rulecount)),
       prepare_comp output input desc_comp, 
       Error("internal error: no valid rule has been selected"))
      
  in
  List.fold_left g (Error("no error")) breakdowns
;;



let code_of_lib (lib : lib) : code = 
  let f (rstep_partitioned : rstep_partitioned) =
    let (name, rstep, cold, reinit, hot, breakdowns) = rstep_partitioned in 
    let output = "Y" in
    let input = "X" in
    Class (name,
	   List.map (function x -> Var(Int, Spl.string_of_intexpr x)) (IntExprSet.elements cold),
	   List.map (function x -> Var(Int, Spl.string_of_intexpr x)) (IntExprSet.elements reinit),
	   List.map (function x -> Var(Int, Spl.string_of_intexpr x)) (IntExprSet.elements hot),
	   cons_code_of_rstep_partitioned rstep_partitioned,
	   comp_code_of_rstep_partitioned rstep_partitioned output input,
	   output,
	   input
    )
  in
  Chain (List.map f lib)
;;

