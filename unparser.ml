open Spl
;;

open Codegen
;;

let rec white (n:int) : string =
  if (n <= 0) then
    ""
  else
    " "^(white (n-1))
;;

let rec string_of_ctype (t : ctype) : string =
  match t with
  |Int -> "int"
  (* |Env(rs) -> "env<" ^ rs ^ ">" *)
;;

type unparse_type =
  Prototype
| Implementation
;;

let rec string_of_intrvalue (intrvalue:intrvalue) : string = 
  match intrvalue with
    ContentsOf Var(_, name) -> name
  | ValueOf intexpr -> string_of_intexpr intexpr
;;

let rec string_of_envrvalue (envrvalue:envrvalue) : string = 
  match envrvalue with
    CreateEnv(name,args) -> "new "^name^"("^(String.concat ", " (List.map string_of_intrvalue args))^")"
;;

let rec string_of_envlvalue (envlvalue:envlvalue) : string = 
  match envlvalue with
    Into Var(Env(rs),name) -> "(cast<"^rs^" *>("^name^"))"
  | Nth(Var(Env(rs), name),count) ->"(cast<"^rs^" *>("^name^")+"^(string_of_intrvalue count)^")"
;;
 
let rec string_of_boolrvalue (boolrvalue:boolrvalue) : string =
  match boolrvalue with
    Equal(a,b) -> "(" ^ (string_of_intrvalue a) ^ " == " ^ (string_of_intrvalue b) ^ ")"
  | BoolValueOf(boolexpr) -> string_of_boolexpr boolexpr
;;

let rec cpp_string_of_code (unparse_type:unparse_type) (n:int) (code : code) : string =
  match code with
    Class(name,cold,reinit,hot,cons,comp) -> 
      let cons_args = (List.map (fun var -> 
	let Var(ctype, name) = var in (string_of_ctype (ctype))^" "^name
      ) (cold@reinit)) in
      let comp_args = (List.map (fun var -> 
	let Var(ctype, name) = var in (string_of_ctype (ctype))^" "^name
      ) hot) in
      (match unparse_type with
	Prototype -> (white n) ^ "struct "^name^" : public RS {\n" 
	  ^ (white (n+4)) ^ "int _rule;\n" 
	  ^ (white (n+4)) ^ "char *_dat;\n" 
	  ^ (String.concat "" (List.map (fun x -> (white (n+4))^x^";\n") cons_args))^ (white (n+4))
      | Implementation -> (white n) ^ name ^ "::")
      ^ name ^ "(" ^ (String.concat ", " cons_args)^")" ^ (match unparse_type with
	Prototype -> ";\n"
      | Implementation -> "{\n"^(cpp_string_of_code unparse_type (n+4) cons)^(white n)^"}\n")
      ^ (match unparse_type with
      | Prototype -> (white (n+4))^"void "
      | Implementation -> (white (n))^"void "^name ^ "::")
      ^ "compute(" ^ (String.concat ", " ("double* Y"::"double* X"::comp_args)) ^ ")"^ (match unparse_type with
	Prototype -> ";\n"
      | Implementation -> "{\n"^(cpp_string_of_code unparse_type (n+4) comp)^(white n)^"}\n")
      ^ (match unparse_type with
	Prototype -> (white n) ^ "};\n\n"
      | Implementation -> "\n")

	
  | Chain l -> String.concat "" (List.map (cpp_string_of_code unparse_type n) l)
  | IntAssign(Var(_, nameL), rvalue) -> (white n) ^ nameL ^ " = "^ (string_of_intrvalue rvalue) ^ ";\n"
  | Noop -> (white n)^"/* noop */\n"
  | Error str -> (white n)^"error(\""^str^"\");\n"
  | If (cond, path_a, path_b) -> (white n)^"if ("^(string_of_boolrvalue cond)^") {\n"^(cpp_string_of_code unparse_type (n+4) path_a)^(white n)^"} else {\n"^(cpp_string_of_code unparse_type (n+4) path_b)^(white n)^"}\n"
  | Loop(Var(Int,name), intrvalue, code) -> (white n)^"for(int "^name^" = 0; "^name^" < "^(string_of_intrvalue intrvalue)^"; "^name^"++){\n"^(cpp_string_of_code unparse_type (n+4) code)^(white n)^"}\n" 
  | Loop(Var(_,_), _, _) -> assert false
  | EnvAssign(lvalue, rvalue) -> (white n) ^ "*" ^ (string_of_envlvalue lvalue) ^ " = "^ (string_of_envrvalue rvalue) ^ ";\n"
  | EnvArrayAllocate(name,rs,int) -> (white n)^name^" = new "^rs^"["^(string_of_intrvalue int)^"];\n"
  | MethodCall(lvalue, methodname,args) -> (white n) ^ (string_of_envlvalue lvalue) ^ " -> "^methodname^"("^(String.concat ", " ("Y"::"X"::(List.map string_of_intrvalue args)))^");\n" 

;;

let string_of_code (n:int) (code : code) : string = 
  "static bool isNotPrime(int a) {return true;} /*FIXME*/\n"
  ^ "static int divisor(int a) {return 1;} /*FIXME*/\n"
  ^ "static void error(char* s) {throw s;}\n"
  ^ "struct RS {};\n\n"
  ^ (cpp_string_of_code Prototype n code)
  ^ (cpp_string_of_code Implementation n code)
;;

