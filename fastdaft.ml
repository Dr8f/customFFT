(******
TYPES
*******)

open Spl;;

open Lib;;

let lib = make_lib [DFT(IVar(IArg(1)))] Algo.algo_cooley_tukey
;;

print_string (string_of_lib lib)
;;
  



(* type envexpr = *)
(*   SimpleEnv of int *)
(* ;; *)

(* let string_of_envexpr (e:envexpr) : string = *)
(*   match e with *)
(*     SimpleEnv i -> "child"^(string_of_int i) *)
(* ;; *)

(* type statement = *)
(* | IntDecl of intexpr *)
(* | IntAssign of intexpr * intexpr *)
(* | EnvAssign of envexpr * string *)
(* | EnvCall of string * envexpr * string *)
(* | If of boolexpr * statement * statement *)
(* | Error of string *)
(* | Chain of statement list *)
(* | Loop of intexpr * intexpr * statement *)
(* | Class of string * intexpr list * intexpr list * statement *)
(* ;; *)

(* type var =  *)
(* | Int of string *)
(* ;; *)

(* let rec type_of (v:var) : string = *)
(*   match v with *)
(*   |Int -> "int" *)
(* ;; *)

(* let rec white (n:int) : string = *)
(*   if (n <= 0) then *)
(*     "" *)
(*   else *)
(*     " "^(white (n-1)) *)
(* ;; *)

(* let rec string_of_statement (n:int) (stmt:statement) : string = *)
(*   match stmt with *)
(*   | IntDecl x -> (white n)^"int "^(string_of_intexpr x)^";\n" *)
(*   | IntAssign (left, right) -> (white n)^(string_of_intexpr left) ^ " = " ^ (string_of_intexpr right) ^ ";\n" *)
(*   | EnvAssign(env,s) -> (white n)^(string_of_envexpr env)^ " = " ^ s ^ ";\n" *)
(*   | EnvCall(name,env,s) -> (white n)^"cast <"^name^" *>("^(string_of_envexpr env) ^ ")" ^ s ^ ";\n" *)

(*   | If (cond, path_a, path_b) -> (white n)^"if ("^(string_of_boolexpr cond)^") {\n"^(string_of_statement (n+4) path_a)^(white n)^"} else {\n"^(string_of_statement (n+4) path_b)^(white n)^"}\n" *)
(*   | Error(str) -> (white n)^"error(\""^str^"\");\n" *)
(*   | Chain l -> String.concat "" (List.map (string_of_statement n) l) *)
(*   | Loop (i,c,exp) -> (white n)^"for(int "^(string_of_intexpr i)^" = 0; "^(string_of_intexpr i)^" < "^(string_of_intexpr c)^"; "^(string_of_intexpr i)^"++){\n"^(string_of_statement (n+4) exp)^(white n)^"}\n" *)
(*   | Class (name, ints, ctor_args, ctor) -> (white n)^"struct "^name^" : public RS {\n"^(String.concat "" (List.map (fun x -> string_of_statement (n+4) (IntDecl x)) ints))^(white (n+4))^name^"("^(String.concat "," (List.map (fun x->string_of_intexpr x) ctor_args))^"){\n"^(string_of_statement (n+8) ctor)^(white (n+4))^"};\n"^(white n)^"};\n" *)
(* ;; *)

(* let class_of_rstep ((name, rstep, cold, reinit, hot, breakdowns): rstep_partitioned) : statement = *)
(*   let arguments_assign = Chain(List.map (fun x -> IntAssign(IVar(ITranscendental ("this->"^(string_of_intexpr x))),x)) (IntExprSet.elements cold)) in  *)
(*   Class(name,  *)
(* 	IVar(ITranscendental("_rule"))::(IntExprSet.elements cold), *)
(* 	(IntExprSet.elements cold), *)
(* 	arguments_assign *)
(*   ) *)
(* ;; *)

(* let classes = List.map class_of_rstep lib *)
(* ;; *)

(* print_string (String.concat "\n\n" (List.map (string_of_statement 0) classes)) *)
(* ;; *)



(* let print_prototype (lib: rstep_partitioned list) : _ = *)
(*   print_string ("static int isNotPrime(int a) {return 1;}\n"); *)
(*   print_string ("static int divisor(int a) {return 1;}\n"); *)
(*   print_string ("static void error(char* s) {throw s;}\n"); *)
(*   print_string ("struct RS {};\n\n"); *)
(*   let f ((name, rstep, cold, reinit, hot, breakdowns ): rstep_partitioned) : _= *)

(*     print_string ("struct "^name^" : public RS {\n"); *)
(*     print_string ("    int _rule;\n"); *)
(*     print_string ("    char *_dat;\n"); *)
(*     print_string (String.concat "" (List.map (fun x -> string_of_statement 4 (IntDecl x)) (IntExprSet.elements cold))); *)
    
(*     let g ((condition, freedoms, desc, desc_with_calls):breakdown) : _ = *)
(*       let h (l,r) = *)
(* 	print_string ((string_of_statement 4) (IntDecl(l))) *)
(*       in *)
(*       List.iter h freedoms *)
(*     in *)
(*     List.iter g breakdowns; *)

(*     print_string ("    "^name^"("^(String.concat ", " (List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements cold)))^");\n"); *)
(*     print_string ("    void compute("^(String.concat ", " ("double* Y"::"double* X"::(List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements hot))))^");\n"); *)
(*     print_string ("};\n\n") *)
(*   in *)
(*   List.iter f lib; *)
(* in *)
(* print_prototype lib *)
(* ;; *)

(* let print_content (lib: rstep_partitioned list) : _ = *)
(*   let f ((name,rstep, cold, reinit, hot, breakdowns ): rstep_partitioned) : _= *)
(*     print_string(name^"::"^name^"("^(String.concat ", " (List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements cold)))^") {\n"); *)
(*     let arguments_assign = Chain(List.map (fun x -> IntAssign(IVar(ITranscendental ("this->"^(string_of_intexpr x))),x)) (IntExprSet.elements cold)) in *)
(*     let envcount = ref 0 in *)
(*     let prepare_env_cons (rs:string) (cold:intexpr list) (reinit:intexpr list) : statement = *)
(*       envcount := !envcount + 1; *)
(*       EnvAssign (SimpleEnv !envcount,("new "^rs^"("^(String.concat ", " (List.map string_of_intexpr (List.append cold reinit)))^")")) *)
(*     in *)
(*     let rec prepare_cons (e:spl) : statement = *)
(*       match e with *)
(*       |Compose l -> Chain (List.map prepare_cons (List.rev l)) *)
(*       |ISum(i,count,spl) -> Loop(i,count,(prepare_cons spl)) (*FIXME, there's some hoisting*) *)
(*       |ActualCall(callee,cold,reinit,_) -> prepare_env_cons callee cold reinit *)
(*       | _ -> Error("nop") *)
(*     in *)
(*     let rulecount = ref 0 in *)
(*     let g (stmt:statement) ((condition,freedoms,desc,desc_with_calls):breakdown) : statement  = *)
(*       let freedom_assigns = List.map (fun (l,r)->IntAssign(l,r)) freedoms in *)
(*       rulecount := !rulecount + 1; *)
(*       If(condition,(Chain( freedom_assigns @ [IntAssign(IVar(ITranscendental "_rule"),IConstant !rulecount)] @ [prepare_cons desc_with_calls])),(Error("no applicable rules"))) *)
(*     in *)
(*     let code_cons = List.fold_left g (Error("no error")) breakdowns in *)
(*     print_string ((string_of_statement 4) (Chain (arguments_assign::[code_cons]))); *)
(*     print_string("}\n\n"); *)


(*     print_string ("void "^name^"::compute("^(String.concat ", " ("double* Y"::"double* X"::(List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements hot))))^"){\n"); *)
(*     let prepare_env_body (rs:string) (hot:intexpr list) : statement = *)
(*       envcount := !envcount + 1; (*FIXME the arrays they are not correct*) *)
(*       EnvCall (rs, SimpleEnv !envcount,("->compute("^(String.concat ", " (List.map string_of_intexpr hot))^")")) *)
(*     in *)
(*     let rec prepare_body (e:spl) : statement = *)
(*       match e with *)
(*       |Compose l -> Chain (List.map prepare_body (List.rev l)) *)
(*       |ISum(i,count,spl) -> Loop(i,count,(prepare_body spl)) (*FIXME, there's some hoisting*) *)
(*       |ActualCall(callee,_,_,hot) -> prepare_env_body callee hot *)
(*       | _ -> Error("nop") *)
(*     in *)
(*     let g (stmt:statement) ((condition,freedoms,desc,desc_with_calls):breakdown) : statement  = *)
(*       let decls = [Error("decl_buffer")] in *)
(*       envcount := 0; *)
(*       rulecount := !rulecount + 1; *)
(*       If(IntEqual(IVar(ITranscendental "_rule"),IConstant !rulecount),(Chain( decls @ [prepare_body desc_with_calls])),(Error("unknown rule"))) *)
(*     in *)
(*     rulecount := 0; *)
(*     let code_comp = List.fold_left g (Error("no error")) breakdowns in *)
(*     print_string (string_of_statement 4 code_comp); *)
(*     print_string("}\n\n"); *)
(*   in *)
(*   List.iter f lib *)
(* in *)
(* print_content lib *)






