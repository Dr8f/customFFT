open Util;

open Code;

let rec string_of_ctype = (t: Ctype.ctype): string =>
  switch (t) {
  | Ctype.Int => "int"
  | Ctype.Func(r) =>
    "TFunc_T" ++ String.concat("_T", List.map(Ctype.string_of_ctype, r))
  | Ctype.Env(rs) => rs
  | Ctype.Ptr(ctype) => string_of_ctype(ctype) ++ " *"
  | Ctype.Char => "char"
  | Ctype.Complex => "complex_t"
  | Ctype.Void => "void"
  | _ => failwith("unsupported ctype in string_of_ctype")
  };

type unparse_type =
  | Prototype
  | Implementation;

let ctype_of_expr = (e: expr): Ctype.ctype =>
  switch (e) {
  | Var(ctype, _) => ctype
  | _ => failwith("ctype_of_expr, not handled: " ++ string_of_expr(e))
  };

let rec string_of_expr = (expr: expr): string =>
  switch (expr) {
  | Equal(a, b) =>
    "(" ++ string_of_expr(a) ++ " == " ++ string_of_expr(b) ++ ")"
  | New(f) => "new " ++ string_of_expr(f)
  | Nth(expr, count) =>
    string_of_expr(expr) ++ "[" ++ string_of_expr(count) ++ "]"
  | Var(_, name) => name
  | Cast(expr, ctype) =>
    "(reinterpret_cast<"
    ++ string_of_ctype(ctype)
    ++ ">("
    ++ string_of_expr(expr)
    ++ "))"
  | MethodCall(expr, methodname, args) =>
    string_of_expr(expr)
    ++ " -> "
    ++ methodname
    ++ "("
    ++ String.concat(", ", List.map(string_of_expr, args))
    ++ ")"
  | FunctionCall(functionname, args) =>
    functionname
    ++ "("
    ++ String.concat(", ", List.map(string_of_expr, args))
    ++ ")"
  | Plus(a, b) =>
    "(" ++ string_of_expr(a) ++ " + " ++ string_of_expr(b) ++ ")"
  | Minus(a, b) =>
    "(" ++ string_of_expr(a) ++ " - " ++ string_of_expr(b) ++ ")"
  | Mul(a, b) =>
    "(" ++ string_of_expr(a) ++ " * " ++ string_of_expr(b) ++ ")"
  | Mod(a, b) =>
    "(" ++ string_of_expr(a) ++ " % " ++ string_of_expr(b) ++ ")"
  | Divide(a, b) =>
    "(" ++ string_of_expr(a) ++ " / " ++ string_of_expr(b) ++ ")"
  | UniMinus(a) => "-(" ++ string_of_expr(a) ++ ")"
  | IConst(a) => string_of_int(a)
  | AddressOf(a) => "(&" ++ string_of_expr(a) ++ ")"
  };

let make_signatures = (l: list('a)): list(string) =>
  List.map(
    expr =>
      string_of_ctype(ctype_of_expr(expr)) ++ " " ++ string_of_expr(expr),
    l,
  );

let rec cpp_string_of_code =
        (unparse_type: unparse_type, n: int, code: code): string =>
  switch (code) {
  | Class(name, super, privates, methods) =>
    (
      switch (unparse_type) {
      | Prototype =>
        white(n)
        ++ "struct "
        ++ name
        ++ " : public "
        ++ string_of_ctype(super)
        ++ " {\n"
        ++ String.concat(
             "",
             List.map(
               x => white(n + 4) ++ x ++ ";\n",
               make_signatures(privates),
             ),
           )
        ++ white(n + 4)
      | Implementation => white(n) ++ name ++ "::"
      }
    )
    ++ String.concat(
         "",
         List.map(
           x => cpp_string_of_cmethod(unparse_type, n, name, x),
           methods,
         ),
       )
    ++ (
      switch (unparse_type) {
      | Prototype =>
        white(n)
        ++ "private:"
        ++ "\n"
        ++ white(n + 4)
        ++ name
        ++ "(const "
        ++ name
        ++ "&);"
        ++ "\n"
        ++ white(n + 4)
        ++ name
        ++ "& operator=(const "
        ++ name
        ++ "&);"
        ++ "\n"
        ++ white(n)
        ++ "};\n\n"
      | Implementation => "\n"
      }
    )

  | Chain(l) =>
    white(n)
    ++ "{\n"
    ++ String.concat(
         "",
         List.map(cpp_string_of_code(unparse_type, n + 4), l),
       )
    ++ white(n)
    ++ "}\n"
  | PlacementNew(l, r) =>
    white(n)
    ++ "new ("
    ++ string_of_expr(l)
    ++ ") "
    ++ string_of_expr(r)
    ++ ";\n"
  | Assign(l, r) =>
    white(n) ++ string_of_expr(l) ++ " = " ++ string_of_expr(r) ++ ";\n"
  | Noop => white(n) ++ "/* noop */\n"
  | ErrorMsg(str) => white(n) ++ "error(\"" ++ str ++ "\");\n"
  | If(cond, path_a, path_b) =>
    white(n)
    ++ "if ("
    ++ string_of_expr(cond)
    ++ ") {\n"
    ++ cpp_string_of_code(unparse_type, n + 4, path_a)
    ++ white(n)
    ++ "} else {\n"
    ++ cpp_string_of_code(unparse_type, n + 4, path_b)
    ++ white(n)
    ++ "}\n"
  | Loop(var, expr, code) =>
    white(n)
    ++ "for(int "
    ++ string_of_expr(var)
    ++ " = 0; "
    ++ string_of_expr(var)
    ++ " < "
    ++ string_of_expr(expr)
    ++ "; "
    ++ string_of_expr(var)
    ++ "++){\n"
    ++ cpp_string_of_code(unparse_type, n + 4, code)
    ++ white(n)
    ++ "}\n"
  | ArrayAllocate(expr, elttype, int) =>
    white(n)
    ++ string_of_expr(expr)
    ++ " = ("
    ++ string_of_ctype(Ctype.Ptr(elttype))
    ++ ") malloc (sizeof("
    ++ string_of_ctype(elttype)
    ++ ") * "
    ++ string_of_expr(int)
    ++ ");\n"
  | ArrayDeallocate(buf, _) =>
    white(n) ++ "free(" ++ string_of_expr(buf) ++ ");\n"
  | Return(expr) => white(n) ++ "return " ++ string_of_expr(expr) ++ ";\n"
  | Declare(expr) =>
    white(n)
    ++ string_of_ctype(ctype_of_expr(expr))
    ++ " "
    ++ string_of_expr(expr)
    ++ ";\n"
  | Ignore(expr) => white(n) ++ string_of_expr(expr) ++ ";\n"
  }

and cpp_string_of_cmethod =
    (unparse_type: unparse_type, n: int, name: string, cmethod: cmethod)
    : string =>
  switch (cmethod) {
  | Method(return_type, method_name, args, code) =>
    (
      switch (unparse_type) {
      | Prototype => white(n + 4) ++ string_of_ctype(return_type) ++ " "
      | Implementation =>
        white(n) ++ string_of_ctype(return_type) ++ " " ++ name ++ "::"
      }
    )
    ++ method_name
    ++ "("
    ++ String.concat(", ", make_signatures(args))
    ++ ")"
    ++ (
      switch (unparse_type) {
      | Prototype => ";\n"
      | Implementation =>
        "{\n"
        ++ cpp_string_of_code(unparse_type, n + 4, code)
        ++ white(n)
        ++ "}\n"
      }
    )
  | Constructor(args, code) =>
    name
    ++ "("
    ++ String.concat(", ", make_signatures(args))
    ++ ")"
    ++ (
      switch (unparse_type) {
      | Prototype => ";\n"
      | Implementation =>
        "\n"
        ++ white(n + 4)
        ++ ": "
        ++ String.concat(
             ", ",
             List.map(
               x => string_of_expr(x) ++ "(" ++ string_of_expr(x) ++ ")",
               args,
             ),
           )
        ++ " {\n"
        ++ cpp_string_of_code(unparse_type, n + 4, code)
        ++ white(n)
        ++ "}\n"
      }
    )
  };

let string_of_codes = (n: int, codes: list(code)): string =>
  "#include <new>\n"
  ++ "#include <string>\n"
  ++ "#include <stdlib.h>\n"
  ++ "#include <complex>\n\n"
  ++ "#include <vector>\n\n"
  ++ "static void error(std::string s) {throw s;}\n"
  ++ "// standard Eratosthene sieve\n"
  ++ "std::vector<std::pair<int, int> > _prime_factorization(int c){\n"
  ++ "    std::vector<std::pair<int, int> > v;\n"
  ++ "    int freq=0;\n"
  ++ "\n"
  ++ "    /* zero has no divisors */\n"
  ++ "    if(c==0) return v;\n"
  ++ "\n"
  ++ "    while ((c%2)==0) {\n"
  ++ "        freq++;\n"
  ++ "        c = c/2;\n"
  ++ "    }\n"
  ++ "    if (freq>0){\n"
  ++ "        std::pair<int, int> p(2, freq);\n"
  ++ "        v.push_back(p);\n"
  ++ "    }\n"
  ++ "\n"
  ++ "    for(int i=3; i<=(sqrt((double)c)+1); i+=2) {\n"
  ++ "        freq = 0;\n"
  ++ "        while ((c%i) == 0) {\n"
  ++ "            freq++;\n"
  ++ "            c = c/i;\n"
  ++ "        }\n"
  ++ "        if (freq>0){\n"
  ++ "            std::pair<int, int> p(i, freq);\n"
  ++ "            v.push_back(p);\n"
  ++ "        }\n"
  ++ "\t}\n"
  ++ "\n"
  ++ "    if (c > 1){\n"
  ++ "        std::pair<int, int> p(c, 1);\n"
  ++ "        v.push_back(p);\n"
  ++ "    }\n"
  ++ "    return v;\n"
  ++ "    }\n"
  ++ "\n"
  ++ "\n"
  ++ "//FIXME: this just picks a random divisor, good but not good enough for autolib\n"
  ++ "static int IDivisor(int n) {\n"
  ++ "  std::vector<std::pair<int, int> > fac = _prime_factorization(n);\n"
  ++ "  \n"
  ++ "  int output = 1;\n"
  ++ "  while ((output == 1)||(output == n)){\n"
  ++ "    output = 1;\n"
  ++ "    for (int i=0;i<fac.size();i++){\n"
  ++ "      output *= pow(fac[i].first, (rand()%(fac[i].second + 1)));\n"
  ++ "    }\n"
  ++ "  }\n"
  ++ "  return output;\n"
  ++ "}\n"
  ++ "\n"
  ++ "\n"
  ++ "bool IsPrime(int n) {\n"
  ++ "    std::vector<std::pair<int, int> > fac = _prime_factorization(n);\n"
  ++ "    // n = n^1, list contains (prime, power) entries\n"
  ++ "    return (fac.size()==1 && fac[0].first==n);\n"
  ++ "}\n"
  ++ "#define complex_t std::complex<float>\n"
  ++ "#define PI    3.14159265358979323846f\n"
  ++ "#define __I__ (complex_t(0,1))\n"
  ++ "static complex_t omega(int N, int k) { return cosf(2*PI*k/N) + __I__ * sinf(2*PI*k/N); }\n"
  ++ "struct RS { virtual ~RS(){}};\n"
  ++ "template<class T> struct TFunc_TInt_T : public RS { virtual T at(int) = 0; };\n"
  ++ "template<class T> struct TFunc_TInt_TInt_T : public RS { virtual T at(int,int) = 0; };\n"
  ++ "struct TFunc_TInt_TComplex : public TFunc_TInt_T<complex_t> {};\n\n"
  ++ "struct TFunc_TInt_TInt_TComplex : public TFunc_TInt_TInt_T<complex_t> {};\n\n"
  ++ String.concat("", List.map(cpp_string_of_code(Prototype, n), codes))
  ++ String.concat(
       "",
       List.map(cpp_string_of_code(Implementation, n), codes),
     );
