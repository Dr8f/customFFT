open Spl
;;

open Lib
;;

type envexpr =
  SimpleEnv of int
;;

let string_of_envexpr (e:envexpr) : string =
  match e with
    SimpleEnv i -> "child"^(string_of_int i)
;;

type statement = 
| IntDecl of intexpr 
| Chain of statement list
| IntAssign of intexpr * intexpr
| EnvAssign of envexpr * string
| Loop of intexpr * intexpr * statement 
| Error2 of string
| If2 of boolexpr * statement * statement
| EnvCall of string * envexpr * string
;;

let rec white (n:int) : string =
  if (n <= 0) then
    ""
  else
    " "^(white (n-1))
;;

let rec string_of_statement (n:int) (stmt:statement) : string =
  match stmt with
  | IntDecl x -> (white n)^"int "^(string_of_intexpr x)^";\n"
  | Chain l -> String.concat "" (List.map (string_of_statement n) l)
  | IntAssign (left, right) -> (white n)^(string_of_intexpr left) ^ " = " ^ (string_of_intexpr right) ^ ";\n"
  | EnvAssign(env,s) -> (white n)^(string_of_envexpr env)^ " = " ^ s ^ ";\n" 
  | Loop (i,c,exp) -> (white n)^"for(int "^(string_of_intexpr i)^" = 0; "^(string_of_intexpr i)^" < "^(string_of_intexpr c)^"; "^(string_of_intexpr i)^"++){\n"^(string_of_statement (n+4) exp)^(white n)^"}\n" 
  | Error2(str) -> (white n)^"error(\""^str^"\");\n"
  | If2 (cond, path_a, path_b) -> (white n)^"if ("^(string_of_boolexpr cond)^") {\n"^(string_of_statement (n+4) path_a)^(white n)^"} else {\n"^(string_of_statement (n+4) path_b)^(white n)^"}\n"
  | EnvCall(name,env,s) -> (white n)^"cast <"^name^" *>("^(string_of_envexpr env) ^ ")" ^ s ^ ";\n"
;;


let build_header () : string = 
  "static bool isNotPrime(int a) {return true;} /*FIXME*/ \n"
  ^ "static int divisor(int a) {return 1;} /*FIXME*/ \n"
  ^ "static void error(char* s) {throw s;}\n"
  ^ "struct RS {};\n\n"
;;

let build_prototype ((name, rstep, cold, reinit, hot, breakdowns ): rstep_partitioned) = 
  let g ((condition, freedoms, desc, desc_with_calls):breakdown) : string =
    let h (l,_) : string =
      string_of_statement 4 (IntDecl(l))
    in
    String.concat "" (List.map h freedoms)
  in
  "struct "^name^" : public RS {\n"
  ^ "    int _rule;\n"
  ^ "    char *_dat;\n"
  ^ (String.concat "" (List.map (fun x -> string_of_statement 4 (IntDecl x)) (IntExprSet.elements cold)))
  ^ (String.concat "" (List.map g breakdowns))
  ^ "    "^name^"("^(String.concat ", " (List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements cold)))^");\n"
  ^ "    void compute("^(String.concat ", " ("double* Y"::"double* X"::(List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements hot))))^");\n"
  ^"};\n\n"
;;

let build_prototypes (lib: lib) : string =
  String.concat "" (List.map build_prototype lib)
;;

let build_implementation ((name, rstep, cold, reinit, hot, breakdowns ): rstep_partitioned) =
  (* FIXME : should be an assignment to this->u1 = u1 *)
  let arguments_assign = Chain(List.map (fun x -> IntAssign(x,x)) (IntExprSet.elements cold)) in 
    let envcount = ref 0 in
    let prepare_env_cons (rs:string) (cold:intexpr list) (reinit:intexpr list) : statement =
      envcount := !envcount + 1;
      EnvAssign (SimpleEnv !envcount,("new "^rs^"("^(String.concat ", " (List.map string_of_intexpr (List.append cold reinit)))^")"))
    in
    let rec prepare_cons (e:spl) : statement =
      match e with
      |Compose l -> Chain (List.map prepare_cons (List.rev l))
      |ISum(i,count,spl) -> Loop(i,count,(prepare_cons spl)) (*FIXME, there's some hoisting*)
      |PartitionnedCall(callee,cold,reinit,_) -> prepare_env_cons callee cold reinit
      | _ -> Error2("nop")
    in
    let rulecount = ref 0 in
    let g (stmt:statement) ((condition,freedoms,desc,desc_with_calls):breakdown) : statement  =
      let freedom_assigns = List.map (fun (l,r)->IntAssign(l,r)) freedoms in
      rulecount := !rulecount + 1;
      (* FIXME: [IntAssign(IVar(ITranscendental "_rule"),IConstant !rulecount)] *)
      If2(condition,(Chain( freedom_assigns @ [prepare_cons desc_with_calls])),(Error2("no applicable rules")))
    in
  let code_cons = List.fold_left g (Error2("no error")) breakdowns in 
  let prepare_env_body (rs:string) (hot:intexpr list) : statement =
    envcount := !envcount + 1; (*FIXME the arrays they are not correct*)
    EnvCall (rs, SimpleEnv !envcount,("->compute("^(String.concat ", " (List.map string_of_intexpr hot))^")"))
  in
  let rec prepare_body (e:spl) : statement =
    match e with
    |Compose l -> Chain (List.map prepare_body (List.rev l))
    |ISum(i,count,spl) -> Loop(i,count,(prepare_body spl)) (*FIXME, there's some hoisting*)
    |PartitionnedCall(callee,_,_,hot) -> prepare_env_body callee hot
    | _ -> Error2("nop")
  in
  let g (stmt:statement) ((condition,freedoms,desc,desc_with_calls):breakdown) : statement  =
    let decls = [Error2("decl_buffer")] in
    envcount := 0;
    rulecount := !rulecount + 1;
    (* FIXME
    If2(IntEqual(IVar(ITranscendental "_rule"),IConstant !rulecount),(Chain( decls @ [prepare_body desc_with_calls])),(Error2("unknown rule")))*)
    Error2("FIXME")
  (* FIXME rulecount := 0; *)
  in
  let code_comp = List.fold_left g (Error2("no error")) breakdowns in 



  name^"::"^name^"("^(String.concat ", " (List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements cold)))^") {\n"
  ^ string_of_statement 4 (Chain (arguments_assign::[code_cons]))
  ^ "}\n\n"

  ^ "void "^name^"::compute("^(String.concat ", " ("double* Y"::"double* X"::(List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements hot))))^"){\n"
    ^ string_of_statement 4 code_comp
    ^ "}\n\n"

;;

let build_implementations (lib: lib) : string =
  String.concat "" (List.map build_implementation lib)
;;

let string_of_lib (lib: lib) : string =
  (build_header () )^(build_prototypes lib)^(build_implementations lib)
  (* String.concat "" (List.map string_of_rstep_partitioned lib) *)
;;



(**********************************************)

open Codegen
;;

let rec string_of_ctype (t : ctype) : string =
  match t with
  |Int -> "int"
;;

type unparse_type =
  Prototype
| Implementation
;;

let rec cpp_string_of_code (unparse_type:unparse_type) (n:int) (code : code) : string =
  match code with
    Class(name,vars,cons) -> 
      let colds = (List.map (fun var -> 
	let Var(ctype, name) = var in (string_of_ctype (ctype))^" "^name
      ) vars) in
      (match unparse_type with
	Prototype -> (white n) ^ "struct "^name^" : public RS {\n" 
	  ^ (white (n+4)) ^ "int _rule;\n" 
	  ^ (white (n+4)) ^ "char *_dat;\n" 
	  ^ (String.concat "" (List.map (fun x -> (white (n+4))^x^";\n") colds))^ (white (n+4))
      | Implementation -> (white n) ^ name ^ "::")
      ^ name ^ "(" ^ (String.concat ", " colds)^")" ^ (match unparse_type with
	Prototype -> ";\n"
      | Implementation -> "{\n"^(cpp_string_of_code unparse_type (n+4) cons)^(white n)^"}\n")
      ^ (match unparse_type with
	  Prototype -> (white n) ^ "};\n\n"
      | Implementation -> "\n")

	
  | Chain l -> String.concat "" (List.map (cpp_string_of_code unparse_type n) l)
  | Assign(Var(_, nameL),Var(_, nameR)) -> (white n) ^ nameL ^ " = " ^ nameR ^ ";\n"
  | Noop -> (white n)^"/* noop */\n"
  | Error str -> (white n)^"error(\""^str^"\");\n"
  | If (cond, path_a, path_b) -> (white n)^"if ("^(string_of_boolexpr cond)^") {\n"^(cpp_string_of_code unparse_type (n+4) path_a)^(white n)^"} else {\n"^(cpp_string_of_code unparse_type (n+4) path_b)^(white n)^"}\n"
;;

let string_of_code (n:int) (code : code) : string = 
  (cpp_string_of_code Prototype n code)
  ^(cpp_string_of_code Implementation n code)
;;

