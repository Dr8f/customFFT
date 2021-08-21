open Util;

open Ctype;

/*********************************************
 	 TYPES
 *********************************************/

type expr =
  | Var(ctype, string)
  | Nth(expr, expr)
  | Cast(expr, ctype)
  | Equal(expr, expr)
  | New(expr)
  | Mul(expr, expr)
  | Plus(expr, expr)
  | Minus(expr, expr)
  | UniMinus(expr)
  | Mod(expr, expr)
  | Divide(expr, expr)
  | FunctionCall(string /*functionname*/, list(expr)) /*arguments*/
  | MethodCall(expr /*object*/, string /*method name*/, list(expr)) /*arguments*/
  | IConst(int)
  | AddressOf(expr);

type cmethod =
  | Constructor(list(expr) /*args*/, code)
  | Method(
      ctype /*return type*/,
      string /* functionname */,
      list(expr) /* args*/,
      code,
    )
and code =
  | Class(
      string /*class name*/,
      ctype /*class template from which it is derived*/,
      list(expr) /*member variables*/,
      list(cmethod),
    ) /*methods*/
  | Chain(list(code))
  | Noop
  | ErrorMsg(string)
  | Assign(expr /*dest*/, expr) /*origin*/
  | ArrayAllocate(expr /*pointer*/, ctype /*element type*/, expr) /*element count*/
  | PlacementNew(expr /*address*/, expr) /*content*/
  | If(expr /*condition*/, code /*true branch*/, code) /*false branch*/
  | Loop(expr /*loop variable*/, expr /*count*/, code)
  | ArrayDeallocate(expr /*pointer*/, expr) /*element count*/
  | Return(expr)
  | Declare(expr)
  | Ignore(expr); /*expression with side effect*/

module ExprMap =
  Map.Make({
    type t = expr;
    let compare = Stdlib.compare;
  });

module ExprSet =
  Set.Make({
    let compare = Stdlib.compare;
    type t = expr;
  });

let rec ctype_of_expr = (e: expr): ctype => {
  let deref = (c: ctype): ctype =>
    switch (c) {
    | Ptr(c) => c
    | _ => failwith("Cannot dereference a non-pointer type")
    };
  switch (e) {
  | Var(ctype, _) => ctype
  | Nth(expr, _) => deref(ctype_of_expr(expr))
  | Cast(_, ctype) => ctype
  | Equal(_) => Bool
  | Mul(a, b)
  | Plus(a, b)
  | Minus(a, b)
  | Mod(a, b)
  | Divide(a, b) =>
    let (at, bt) = (ctype_of_expr(a), ctype_of_expr(b));
    if (at == bt) {
      at;
    } else {
      failwith("type lattice not implemented yet");
    };
  | UniMinus(expr) => ctype_of_expr(expr)
  | IConst(_) => Int
  | New(_)
  | FunctionCall(_)
  | MethodCall(_)
  | AddressOf(_) => failwith("not implemented yet")
  };
};

/*********************************************
 	 PRINTING
 *********************************************/

let rec string_of_expr = (expr: expr): string =>
  switch (expr) {
  | Equal(a, b) =>
    "Equal(" ++ string_of_expr(a) ++ ", " ++ string_of_expr(b) ++ ")"
  | New(f) => "New(" ++ string_of_expr(f) ++ ")"
  | Nth(expr, count) =>
    "Nth(" ++ string_of_expr(expr) ++ ", " ++ string_of_expr(count) ++ ")"
  | Var(a, b) =>
    "Var(" ++ string_of_ctype(a) ++ ", \"" ++ b ++ "\")"
  | Cast(expr, ctype) =>
    "Cast(" ++ string_of_expr(expr) ++ ", " ++ string_of_ctype(ctype) ++ ")"
  | MethodCall(expr, methodname, args) =>
    "MethodCall("
    ++ string_of_expr(expr)
    ++ ", \""
    ++ methodname
    ++ "\", ["
    ++ String.concat("; ", List.map(string_of_expr, args))
    ++ "])"
  | FunctionCall(functionname, args) =>
    "FunctionCall(\""
    ++ functionname
    ++ "\", ["
    ++ String.concat("; ", List.map(string_of_expr, args))
    ++ "])"
  | Plus(a, b) =>
    "Plus(" ++ string_of_expr(a) ++ ", " ++ string_of_expr(b) ++ ")"
  | Minus(a, b) =>
    "Minus(" ++ string_of_expr(a) ++ ", " ++ string_of_expr(b) ++ ")"
  | Mul(a, b) =>
    "Mul(" ++ string_of_expr(a) ++ ", " ++ string_of_expr(b) ++ ")"
  | Mod(a, b) =>
    "Mod(" ++ string_of_expr(a) ++ ", " ++ string_of_expr(b) ++ ")"
  | Divide(a, b) =>
    "Divide(" ++ string_of_expr(a) ++ ", " ++ string_of_expr(b) ++ ")"
  | UniMinus(a) => "UniMinus(" ++ string_of_expr(a) ++ ")"
  | IConst(a) => "IConst(" ++ string_of_int(a) ++ ")"
  | AddressOf(a) => "AddressOf(" ++ string_of_expr(a) ++ ")"
  };

let rec string_of_code = (n: int, code: code): string =>
  white(n)
  ++ (
    switch (code) {
    | Chain(l) =>
      "Chain( [\n"
      ++ String.concat(";\n", List.map(string_of_code(n + 4), l))
      ++ "\n"
      ++ white(n)
      ++ "] )"
    | PlacementNew(l, r) =>
      "PlacementNew("
      ++ string_of_expr(l)
      ++ ", "
      ++ string_of_expr(r)
      ++ ")"
    | Assign(l, r) =>
      "Assign(" ++ string_of_expr(l) ++ ", " ++ string_of_expr(r) ++ ")"
    | Loop(var, expr, code) =>
      "Loop("
      ++ string_of_expr(var)
      ++ ", "
      ++ string_of_expr(expr)
      ++ ", \n"
      ++ string_of_code(n + 4, code)
      ++ "\n"
      ++ white(n)
      ++ ")"
    | ArrayAllocate(expr, elttype, int) =>
      "ArrayAllocate("
      ++ string_of_expr(expr)
      ++ ", "
      ++ string_of_ctype(elttype)
      ++ ", "
      ++ string_of_expr(int)
      ++ ")"
    | ArrayDeallocate(buf, size) =>
      "ArrayDeallocate("
      ++ string_of_expr(buf)
      ++ ", "
      ++ string_of_expr(size)
      ++ ")"
    | Return(expr) => "Return(" ++ string_of_expr(expr) ++ ")"
    | Declare(expr) => "Declare(" ++ string_of_expr(expr) ++ ")"
    | Noop => "Noop"
    | _ => failwith("string_of_code, not handled")
    }
  );

/*********************************************
 	 METARULES
 *********************************************/

let meta_transform_code_on_code =
    (recursion_direction: recursion_direction): ((code => code, code) => code) => {
  let z = (g: code => code, e: code): code =>
    switch (e) {
    | Chain(l) => Chain(List.map(g, l))
    | Loop(var, expr, code) =>
      Loop(var, expr, g(code))
    | PlacementNew(_)
    | Assign(_)
    | ArrayAllocate(_)
    | ArrayDeallocate(_)
    | Return(_)
    | Declare(_)
    | Noop => e
    | _ => failwith("string_of_code, not handled " ++ string_of_code(0, e))
    };

  recursion_transform(recursion_direction, z);
};

let meta_collect_code_on_code = (f: code => list('a)): (code => list('a)) => {
  let z = (g: code => list('a), e: code): list('a) =>
    switch (e) {
    | Chain(l) => List.flatten(List.map(g, l))
    | Loop(_, _, code) => g(code)
    | If(_, true_branch, false_branch) =>
      g(true_branch) @ g(false_branch)
    | _ => []
    };

  recursion_collect(z, f);
};

let meta_collect_expr_on_expr = (f: expr => list('a)): (expr => list('a)) => {
  let z = (g: expr => list('a), e: expr): list('a) =>
    switch (e) {
    | Nth(a, b)
    | Equal(a, b)
    | Mul(a, b)
    | Plus(a, b)
    | Minus(a, b)
    | Mod(a, b)
    | Divide(a, b) => g(a) @ g(b)
    | Cast(a, _)
    | New(a)
    | UniMinus(a)
    | AddressOf(a) => g(a)
    | FunctionCall(_, l) => List.flatten(List.map(g, l))
    | MethodCall(a, _, l) =>
      g(a) @ List.flatten(List.map(g, l))
    | _ => []
    };

  recursion_collect(z, f);
};

let meta_collect_expr_on_code = (f: expr => list('a)): (code => list('a)) => {
  let direct_from_code = (ff: expr => list('a), e: code): list('a) =>
    switch (e) {
    | Assign(dest, orig) => ff(dest) @ ff(orig)
    | ArrayAllocate(pointer, _, elcount) =>
      ff(pointer) @ ff(elcount)
    | PlacementNew(address, content) =>
      ff(address) @ ff(content)
    | If(condition, _, _) => ff(condition)
    | Loop(var, expr, _) => ff(var) @ ff(expr)
    | ArrayDeallocate(pointer, elcount) =>
      ff(pointer) @ ff(elcount)
    | Return(expr)
    | Declare(expr)
    | Ignore(expr) => ff(expr)
    | Noop
    | Chain(_)
    | ErrorMsg(_) => []
    | Class(_, _, _, _) => []
    }; /* not seriously thought after*/

  (e: code) => {
    let ff = meta_collect_expr_on_expr(f);
    (meta_collect_code_on_code(direct_from_code(ff)))(e);
  };
};

let meta_transform_expr_on_expr =
    (recursion_direction: recursion_direction): ((expr => expr, expr) => expr) => {
  let z = (g: expr => expr, e: expr): expr =>
    switch (e) {
    | Equal(a, b) => Equal(g(a), g(b))
    | Plus(a, b) => Plus(g(a), g(b))
    | Minus(a, b) => Minus(g(a), g(b))
    | Mul(a, b) => Mul(g(a), g(b))
    | Cast(expr, ctype) =>
      Cast(g(expr), ctype)
    | Nth(expr, count) =>
      Nth(g(expr), g(count))
    | Var(_)
    | IConst(_) => e
    | x => failwith("Pattern_matching failed:\n" ++ string_of_expr(x))
    };

  recursion_transform(recursion_direction, z);
};

let meta_transform_expr_on_code =
    (recursion_direction: recursion_direction, f: expr => expr)
    : (code => code) => {
  let g = meta_transform_expr_on_expr(recursion_direction, f);
  meta_transform_code_on_code(
    recursion_direction,
    fun
    | Declare(e) => Declare(g(e))
    | Assign(l, r) =>
      Assign(g(l), g(r))
    | Chain(_) as x => x
    | ArrayAllocate(a, ctype, b) =>
      ArrayAllocate(g(a), ctype, g(b))
    | ArrayDeallocate(a, b) =>
      ArrayDeallocate(g(a), g(b))
    | Noop => Noop
    | Loop(var, expr, code) =>
      Loop(g(var), g(expr), code)
    | x =>
      failwith(
        "Pattern_matching failed in meta_transform_expr_on_code:\n"
        ++ string_of_code(0, x),
      ),
  );
};

let substitution_expr_on_expr =
    (target: expr, replacement: expr): (expr => expr) =>
  meta_transform_expr_on_expr(TopDown, e =>
    if (e == target) {
      replacement;
    } else {
      e;
    }
  );

let substitution_expr_on_code =
    (target: expr, replacement: expr): (code => code) =>
  meta_transform_expr_on_code(TopDown, e =>
    if (e == target) {
      replacement;
    } else {
      e;
    }
  );

let substitution_code_on_code =
    (target: code, replacement: code): (code => code) =>
  meta_transform_code_on_code(TopDown, e =>
    if (e == target) {
      replacement;
    } else {
      e;
    }
  );

let gen_var = {
  as _;
  val tbl = ref(StringMap.empty);
  pub get = (ctype: ctype, prefix: string): expr => {
    let count =
      if (StringMap.mem(prefix, tbl^)) {
        StringMap.find(prefix, tbl^) + 1;
      } else {
        1;
      };
    tbl := StringMap.add(prefix, count, tbl^);
    Var(ctype, prefix ++ string_of_int(count));
  }
};

module StringMap = Map.Make(String);

module IntMap =
  Map.Make({
    type t = int;
    let compare = compare;
  });

let meta_chain_code =
    (recursion_direction: recursion_direction, f: list(code) => list(code))
    : (code => code) =>
  meta_transform_code_on_code(
    recursion_direction,
    fun
    | Chain(l) => Chain(f(l))
    | x => x,
  );

let flatten_chain: code => code = (
  {
    let rec f = (l: list(code)): list(code) =>
      switch (l) {
      | [Chain(a), ...tl] => f(a @ tl)
      | [Noop, ...tl] => f(tl)
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_chain_code(BottomUp, f);
  }:
    code => code
);

let empty_chain: code => code = (
  meta_transform_code_on_code(
    BottomUp,
    fun
    | Chain([]) => Noop
    | x => x,
  ):
    code => code
);

let code_rulemap =
  List.fold_left(
    (map, (name, rule)) => StringMap.add(name, rule, map),
    StringMap.empty,
    [("Flatten chain", flatten_chain), ("Empty chain", empty_chain)],
  );

let simplify_code = (f: code): code =>
  apply_rewriting_rules(code_rulemap, f);
