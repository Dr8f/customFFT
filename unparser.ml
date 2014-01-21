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
  |Env(rs) -> rs
  |Ptr(ctype)->(string_of_ctype ctype)^" *"
;;

type unparse_type =
  Prototype
| Implementation
;;

let rec string_of_expr (expr:expr) : string = 
  match expr with
  | IntexprValueOf intexpr -> string_of_intexpr intexpr
  | Equal(a,b) -> "(" ^ (string_of_expr a) ^ " == " ^ (string_of_expr b) ^ ")"
  | BoolValueOf(boolexpr) -> string_of_boolexpr boolexpr
  | IdxfuncValueOf(f)->string_of_idxfunc f
  | CreateEnv(name,args) -> name^"("^(String.concat ", " (List.map string_of_expr (args)))^")"
  | New(f) -> "new "^(string_of_expr f) 
  | Nth(expr, count) ->"("^(string_of_expr expr)^"+"^(string_of_expr count)^")"
  | Var(_, name) -> name
  | Cast(expr, ctype) -> "(reinterpret_cast<"^(string_of_ctype ctype)^">("^(string_of_expr expr)^"))"  
;;
 
let rec cpp_string_of_code (unparse_type:unparse_type) (n:int) (code : code) : string =
  let make_signatures (l:'a list) : string list =
    List.map (fun var -> let Var(ctype, name) = var in (string_of_ctype (ctype))^" "^name) (l)
  in
  match code with
  | FuncEnv(name,args,fargs,code) ->
    (match unparse_type with
      Prototype ->    	   
	"struct "^name^" : public func {\n"
	^(String.concat "" (List.map (fun x -> (white (n+4))^x^";\n") (make_signatures (args@fargs))))
	^(white (n+4))
    | Implementation -> name^"::"
    )^name^"("^(String.concat ", " ((make_signatures args)@(make_signatures fargs)))^")"^
      (match unparse_type with
	Prototype -> ";\n"^(white (n+4))^"virtual "
      | Implementation -> " : \n"
	^ (String.concat (", \n") ((List.map (fun x -> let Var(ctype, name) = x in (white (n+4))^name^"("^name^")") (args@fargs)) ))
	^ "{\n}\n\n"^(white n)
      )
    ^"complex_t "^(match unparse_type with
      Prototype -> ""
    | Implementation -> name^"::"
    )^"at(int t0)"^(match unparse_type with
      Prototype -> ";\n"^"};\n\n"
    | Implementation -> "{\n"^(cpp_string_of_code unparse_type (n+4) code)^"}\n\n"
    )
      
  | Class(name,cold,reinit,hot,funcs,cons,comp,output,input,privates) -> 
    let cons_args = make_signatures (cold@reinit@funcs) in
    (match unparse_type with
      Prototype -> (white n) ^ "struct "^name^" : public RS {\n" 
	^ (white (n+4)) ^ "int _rule;\n" 
	^ (white (n+4)) ^ "char *_dat;\n" 
	^ (String.concat "" (List.map (fun x -> (white (n+4))^x^";\n") (make_signatures privates)))
	^ (String.concat "" (List.map (fun x -> (white (n+4))^x^";\n") cons_args))
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
    ^ "compute(" ^ (String.concat ", " (("complex_t* "^output)::("complex_t* "^input)::(make_signatures hot))) ^ ")"^ (match unparse_type with
      Prototype -> ";\n"
    | Implementation -> "{\n"^(cpp_string_of_code unparse_type (n+4) comp)^(white n)^"}\n")
    ^ (match unparse_type with
      Prototype -> (white n) ^ "private:" ^ "\n"
	^ (white (n+4)) ^ name ^ "(const " ^ name ^ "&);" ^ "\n"
	^ (white (n+4)) ^ name ^ "& operator=(const " ^ name ^"&);" ^ "\n"
	^ "};\n\n"
    | Implementation -> "\n")
      
	
  | Chain l -> String.concat "" (List.map (cpp_string_of_code unparse_type n) l)
  | PlacementNew(l, r) -> (white n)^"new ("^(string_of_expr l)^") "^(string_of_expr r)^";\n" 
  | Assign(l, r) -> (white n) ^ (string_of_expr l) ^ " = "^ (string_of_expr r) ^ ";\n"
  | Noop -> (white n)^"/* noop */\n"
  | Error str -> (white n)^"error(\""^str^"\");\n"
  | If (cond, path_a, path_b) -> (white n)^"if ("^(string_of_expr cond)^") {\n"^(cpp_string_of_code unparse_type (n+4) path_a)^(white n)^"} else {\n"^(cpp_string_of_code unparse_type (n+4) path_b)^(white n)^"}\n"
  | Loop(Var(Int,name), expr, code) -> (white n)^"for(int "^name^" = 0; "^name^" < "^(string_of_expr expr)^"; "^name^"++){\n"^(cpp_string_of_code unparse_type (n+4) code)^(white n)^"}\n" 
  | Loop(Var(_,_), _, _) -> assert false
  | EnvArrayAllocate(expr,rs,int) -> (white n)^(string_of_expr expr)^" = ("^rs^"*) malloc (sizeof("^rs^") * "^(string_of_expr int)^");\n"
  (* | EnvArrayConstruct(expr,expr) -> (white n)^"new ("^(string_of_expr expr)^") "^(string_of_expr expr)^";\n" *)
  | MethodCall(expr, methodname,args, output, input) -> (white n) ^ (string_of_expr expr) ^ " -> "^methodname^"("^(String.concat ", " (output::input::(List.map string_of_expr args)))^");\n" 
  | BufferAllocate(buf, size) -> (white n)^"complex_t * "^buf^" = LIB_MALLOC("^(string_of_expr size)^");\n"
  | BufferDeallocate(buf, size) -> (white n)^"LIB_FREE("^buf^", "^(string_of_expr size)^");\n"
  | Return(i) -> (white n)^"return t"^(string_of_int i)^";\n"
;;

let string_of_code (n:int) (code : code) : string = 
  "#include <new>\n"
  ^ "#include <string>\n"
  ^ "#include <stdlib.h>\n"
  ^ "#include <complex>\n\n"
  ^ "static bool isNotPrime(int ) {return true;} /*FIXME*/\n"
  ^ "static int divisor(int ) {return 1;} /*FIXME*/\n"
  ^ "static void error(std::string s) {throw s;}\n"
  ^ "#define complex_t std::complex<float>\n"
  ^ "complex_t * LIB_MALLOC(size_t size) {return (complex_t *)malloc(size * sizeof(complex_t));}\n"
  ^ "void LIB_FREE(void *ptr, size_t) {free(ptr);}\n"
  ^ "#define PI    3.14159265358979323846f\n"
  ^ "#define __I__ (complex_t(0,1))\n"
  ^ "static complex_t sp_omega(int N, int k) { return cosf(2*PI*k/N) + __I__ * sinf(2*PI*k/N); }\n"
  ^ "struct RS { virtual ~RS(){}};\n"
  ^ "template<class T> struct TFunc_TInt_T : public RS { virtual T at(int) = 0; };\n"
  ^ "struct func : public TFunc_TInt_T<complex_t> {};\n\n"

  ^ "/*\n"
  ^ "d(u1,u2) . h(u3,u1,u5,u6)\n"
  ^ "complex_t Func_1::at(int i){\n"
  ^ "    int x = u5 + u6 * i;\n"
  ^ "    return sp_omega(u1, -(x % u2) * (x / u2));\n"
  ^ "}\n"
  ^ "\n"
  ^ "lambda1 . h(u2,u1,u4,u5)\n"
  ^ "complex_t Func_2::at(int i){\n"
  ^ "    int x = u4 + i*u5;\n"
  ^ "    return lambda1->at(x);\n"
  ^ "}\n"
  ^ "*/\n\n"

  ^ (cpp_string_of_code Prototype n code)
  ^ (cpp_string_of_code Implementation n code)

    


;;

