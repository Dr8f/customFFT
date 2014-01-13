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
  |Func -> "func*"
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
    CreateEnv(name,args,funcs) -> name^"("^(String.concat ", " ((List.map string_of_intrvalue args)@(List.map (function (f:idxfunc) -> "new "^(string_of_idxfunc f)) funcs)))^")"
;;

let rec string_of_envlvalue (envlvalue:envlvalue) : string = 
  match envlvalue with
    Into Var(Env(rs),name) -> "(reinterpret_cast<"^rs^" *>("^name^"))" 
  | Nth(Var(Env(rs), name),count) ->"(reinterpret_cast<"^rs^" *>("^name^")+"^(string_of_intrvalue count)^")"
;;
 
let rec string_of_boolrvalue (boolrvalue:boolrvalue) : string =
  match boolrvalue with
    Equal(a,b) -> "(" ^ (string_of_intrvalue a) ^ " == " ^ (string_of_intrvalue b) ^ ")"
  | BoolValueOf(boolexpr) -> string_of_boolexpr boolexpr
;;

let rec cpp_string_of_code (unparse_type:unparse_type) (n:int) (code : code) : string =
  match code with
    Class(name,cold,reinit,hot,funcs,cons,comp,output,input,children,freedoms) -> 
      let cons_args = (List.map (fun var -> 
	let Var(ctype, name) = var in (string_of_ctype (ctype))^" "^name
      ) (cold@reinit@funcs)) in
      let comp_args = (List.map (fun var -> 
	let Var(ctype, name) = var in (string_of_ctype (ctype))^" "^name
      ) hot) in
      let freedoms_args = (List.map (fun var -> 
	let Var(ctype, name) = var in (string_of_ctype (ctype))^" "^name
      ) freedoms) in
      (match unparse_type with
	Prototype -> (white n) ^ "struct "^name^" : public RS {\n" 
	  ^ (white (n+4)) ^ "int _rule;\n" 
	  ^ (white (n+4)) ^ "char *_dat;\n" 
	  ^ (String.concat "" (List.map (fun x -> (white (n+4))^"RS *"^x^";\n") children))
	  ^ (String.concat "" (List.map (fun x -> (white (n+4))^x^";\n") cons_args))
	  ^ (String.concat "" (List.map (fun x -> (white (n+4))^x^";\n") freedoms_args))
	  ^ (white (n+4))
      | Implementation -> (white n) ^ name ^ "::")
      ^ name ^ "(" ^ (String.concat ", " cons_args)^")" ^ (match unparse_type with
	Prototype -> ";\n"
      | Implementation -> " : \n"
	^ (String.concat (", \n") ((List.map (fun x -> let Var(ctype, name) = x in (white (n+4))^name^"("^name^")") (cold@reinit@funcs)) )) 
	^ " {\n"^(cpp_string_of_code unparse_type (n+4) cons)^(white n)^"}\n")
      ^ (match unparse_type with
      | Prototype -> (white (n+4))^"void "
      | Implementation -> (white (n))^"void "^name ^ "::")
      ^ "compute(" ^ (String.concat ", " (("double* "^output)::("double* "^input)::comp_args)) ^ ")"^ (match unparse_type with
	Prototype -> ";\n"
      | Implementation -> "{\n"^(cpp_string_of_code unparse_type (n+4) comp)^(white n)^"}\n")
      ^ (match unparse_type with
	Prototype -> (white n) ^ "private:" ^ "\n"
	  ^ (white (n+4)) ^ name ^ "(const " ^ name ^ "&);" ^ "\n"
	  ^ (white (n+4)) ^ name ^ "& operator=(const " ^ name ^"&);" ^ "\n"
	  ^ "};\n\n"
      | Implementation -> "\n")

	
  | Chain l -> String.concat "" (List.map (cpp_string_of_code unparse_type n) l)
  | IntAssign(Var(_, nameL), rvalue) -> (white n) ^ nameL ^ " = "^ (string_of_intrvalue rvalue) ^ ";\n"
  | Noop -> (white n)^"/* noop */\n"
  | Error str -> (white n)^"error(\""^str^"\");\n"
  | If (cond, path_a, path_b) -> (white n)^"if ("^(string_of_boolrvalue cond)^") {\n"^(cpp_string_of_code unparse_type (n+4) path_a)^(white n)^"} else {\n"^(cpp_string_of_code unparse_type (n+4) path_b)^(white n)^"}\n"
  | Loop(Var(Int,name), intrvalue, code) -> (white n)^"for(int "^name^" = 0; "^name^" < "^(string_of_intrvalue intrvalue)^"; "^name^"++){\n"^(cpp_string_of_code unparse_type (n+4) code)^(white n)^"}\n" 
  | Loop(Var(_,_), _, _) -> assert false
  | EnvAllocateConstruct(var, rvalue) -> (white n) ^ var ^ " = new "^ (string_of_envrvalue rvalue) ^ ";\n"
  | EnvArrayAllocate(name,rs,int) -> (white n)^name^" = ("^rs^"*) malloc (sizeof("^rs^") * "^(string_of_intrvalue int)^");\n"
  | EnvArrayConstruct(lvalue,rvalue) -> (white n)^"new ("^(string_of_envlvalue lvalue)^") "^(string_of_envrvalue rvalue)^";\n"
  | MethodCall(lvalue, methodname,args, output, input) -> (white n) ^ (string_of_envlvalue lvalue) ^ " -> "^methodname^"("^(String.concat ", " (output::input::(List.map string_of_intrvalue args)))^");\n" 
  | BufferAllocate(buf, size) -> (white n)^"double * "^buf^" = LIB_MALLOC("^(string_of_intrvalue size)^");\n"
  | BufferDeallocate(buf, size) -> (white n)^"LIB_FREE("^buf^", "^(string_of_intrvalue size)^");\n"

(* ^rs^"("^(String.concat ", " (List.map string_of_intrvalue args))^");\n" *)

;;

let string_of_code (n:int) (code : code) : string = 
  "#include <new>\n"
  ^ "#include <string>\n"
  ^ "#include <stdlib.h>\n"
  ^ "#include <complex>\n\n"
  ^ "static bool isNotPrime(int ) {return true;} /*FIXME*/\n"
  ^ "static int divisor(int ) {return 1;} /*FIXME*/\n"
  ^ "static void error(std::string s) {throw s;}\n"
  ^ "double * LIB_MALLOC(size_t size) {return (double *)malloc(size * sizeof(double));}\n"
  ^ "void LIB_FREE(void *ptr, size_t) {free(ptr);}\n"
  ^ "struct RS { virtual ~RS(){}};\n"
  ^ "template<class T> struct TFunc_TInt_T : public RS { virtual T at(int) = 0; };\n"
  ^ "#define complex_t std::complex<double>\n"
  ^ "struct func : public TFunc_TInt_T<complex_t> {};\n\n"

  ^ "struct Func_1 : public func {\n"
  ^ "    Func_1(int a, int b, int c, int d, int e){};\n"
  ^ "  virtual complex_t at(int) {\n"
  ^ "        return 0; /*FIXME*/\n"
  ^ "  }\n"
  ^ "};\n"
  ^ "\n"
  ^ "struct Func_2 : public func {\n"
  ^ "    Func_2(int a, int b, int c, int d, func* f){};\n"
  ^ "  virtual complex_t at(int) {\n"
  ^ "        return 0; /*FIXME*/\n"
  ^ "  }\n"
  ^ "};\n"



  ^ (cpp_string_of_code Prototype n code)
  ^ (cpp_string_of_code Implementation n code)
;;

