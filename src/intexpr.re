open Util;

type intexpr =
  | IConstant(int)
  | IFreedom(int) /* degree of freedom */
  | ILoopCounter(int)
  | IArg(int) /* function argument */
  | IMul(list(intexpr))
  | IPlus(list(intexpr))
  | IDivPerfect(intexpr, intexpr) /* IDivPerfect(i,j) = i / j and j divides i for sure */
  | IDivisor(intexpr) /* IDivisor(i) returns a divisor of i */
  | ICountWrap(int, intexpr); /* internal */

let rec string_of_intexpr = (e: intexpr): string =>
  switch (e) {
  | IConstant(i) =>
    optional_short_print(
      string_of_int(i),
      "IConstant(" ++ string_of_int(i) ++ ")",
    )
  | IMul(l) =>
    optional_short_infix_list_print("IMul", " * ", l, string_of_intexpr)
  | IPlus(l) =>
    optional_short_infix_list_print("IPlus", " + ", l, string_of_intexpr)
  | IDivPerfect(l, r) =>
    optional_short_print(
      string_of_intexpr(l) ++ " / " ++ string_of_intexpr(r),
      "IDivPerfect("
      ++ (string_of_intexpr(l) ++ ", " ++ string_of_intexpr(r))
      ++ ")",
    )
  | ICountWrap(l, r) =>
    "ICountWrap(" ++ string_of_int(l) ++ ", " ++ string_of_intexpr(r) ++ ")"
  | IDivisor(l) => "IDivisor(" ++ string_of_intexpr(l) ++ ")"
  | IFreedom(i) =>
    optional_short_print(
      "d" ++ string_of_int(i),
      "IFreedom(" ++ string_of_int(i) ++ ")",
    )
  | ILoopCounter(i) =>
    optional_short_print(
      "i" ++ string_of_int(i),
      "ILoopCounter(" ++ string_of_int(i) ++ ")",
    )
  | IArg(i) =>
    optional_short_print(
      "u" ++ string_of_int(i),
      "IArg(" ++ string_of_int(i) ++ ")",
    )
  };

let string_of_intexpr_intexpr = ((e, f): (intexpr, intexpr)): string =>
  string_of_intexpr(e) ++ "=" ++ string_of_intexpr(f);

let string_of_intexpr_intmap = (map: IntMap.t(intexpr)): string =>
  "IntexprIntMap("
  ++ String.concat(
       "; ",
       List.map(
         fun
         | (e, f) =>
           "(" ++ string_of_int(e) ++ ", " ++ string_of_intexpr(f) ++ ")",
         IntMap.bindings(map),
       ),
     )
  ++ ")";

let meta_transform_ctx_intexpr_on_intexpr =
    (recursion_direction: recursion_direction)
    : (((list(intexpr), intexpr) => intexpr, intexpr) => intexpr) => {
  let z = (g: intexpr => intexpr, _: list(intexpr), e: intexpr): intexpr =>
    switch (e) {
    | IMul(l) => IMul(List.map(g, l))
    | IPlus(l) => IPlus(List.map(g, l))
    | IDivPerfect(a, b) =>
      IDivPerfect(g(a), g(b))
    | ICountWrap(_, _) => e /*FIXME this seems just wrong*/
    | IDivisor(l) => IDivisor(g(l))
    | IFreedom(_)
    | IArg(_)
    | IConstant(_)
    | ILoopCounter(_) => e
    };

  recursion_transform_ctx(recursion_direction, z);
};

let meta_transform_intexpr_on_intexpr =
    (recursion_direction: recursion_direction, z: intexpr => intexpr)
    : (intexpr => intexpr) =>
  meta_transform_ctx_intexpr_on_intexpr(recursion_direction, _ => z);

let meta_collect_intexpr_on_intexpr =
    (f: intexpr => list('a)): (intexpr => list('a)) => {
  let z = (g: intexpr => list('a), e: intexpr): list('a) =>
    switch (e) {
    | IMul(l) => List.flatten(List.map(g, l))
    | IPlus(l) => List.flatten(List.map(g, l))
    | IDivPerfect(a, b) => g(a) @ g(b)
    | IDivisor(b)
    | ICountWrap(_, b) => g(b)
    | IFreedom(_)
    | IArg(_)
    | IConstant(_)
    | ILoopCounter(_) => []
    };

  recursion_collect(z, f);
};

let meta_iter_intexpr_on_intexpr = (f: intexpr => unit): (intexpr => unit) =>
  (e: intexpr) =>
    ignore(
      meta_collect_intexpr_on_intexpr(
        (e: intexpr) => {
          f(e);
          [];
        },
        e,
      ),
    );

let gen_loop_counter = {
  as _;
  val tbl = ref(0);
  pub get = (): intexpr => {
    tbl := tbl^ + 1;
    ILoopCounter(tbl^);
  }
};

/*********************************************
 	 RULES
 *********************************************/

let meta_multiply_intexpr =
    (
      recursion_direction: recursion_direction,
      f: list(intexpr) => list(intexpr),
    )
    : (intexpr => intexpr) =>
  meta_transform_intexpr_on_intexpr(
    recursion_direction,
    fun
    | IMul(l) => IMul(f(l))
    | x => x,
  );

let meta_addition_intexpr =
    (
      recursion_direction: recursion_direction,
      f: list(intexpr) => list(intexpr),
    )
    : (intexpr => intexpr) =>
  meta_transform_intexpr_on_intexpr(
    recursion_direction,
    fun
    | IPlus(l) => IPlus(f(l))
    | x => x,
  );

let rule_remove_unary_fmul_on_intexpr: intexpr => intexpr = (
  meta_transform_intexpr_on_intexpr(
    BottomUp,
    fun
    | IMul([x]) => x
    | x => x,
  ):
    intexpr => intexpr
);

let rule_multiply_by_one_on_intexpr: intexpr => intexpr = (
  {
    let rec f = (l: list(intexpr)): list(intexpr) =>
      switch (l) {
      | [IConstant(1), ...tl] => f(tl)
      | [a, IConstant(1), ...tl] => f([a, ...tl])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_multiply_intexpr(BottomUp, f);
  }:
    intexpr => intexpr
);

let rule_addition_zero_on_intexpr: intexpr => intexpr = (
  {
    let rec f = (l: list(intexpr)): list(intexpr) =>
      switch (l) {
      | [IConstant(0), ...tl] => f(tl)
      | [a, IConstant(0), ...tl] => f([a, ...tl])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_addition_intexpr(BottomUp, f);
  }:
    intexpr => intexpr
);

let rule_multiply_and_divide_by_the_same_on_intexpr: intexpr => intexpr = (
  {
    let rec f = (l: list(intexpr)): list(intexpr) =>
      switch (l) {
      | [a, IDivPerfect(b, c), ...tl] when a == c =>
        f([b, ...tl])
      | [IDivPerfect(a, b), c, ...tl] when b == c =>
        f([a, ...tl])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_multiply_intexpr(BottomUp, f);
  }:
    intexpr => intexpr
);

let intexpr_rulemap =
  List.fold_left(
    (map, (name, rule)) => StringMap.add(name, rule, map),
    StringMap.empty,
    [
      ("Remove unary fmul", rule_remove_unary_fmul_on_intexpr),
      ("Multiply by one", rule_multiply_by_one_on_intexpr),
      ("Addition zero", rule_addition_zero_on_intexpr),
      (
        "Multiply and divide by the same",
        rule_multiply_and_divide_by_the_same_on_intexpr,
      ),
    ],
  );

let simplify_intexpr = (f: intexpr): intexpr =>
  apply_rewriting_rules(intexpr_rulemap, f);
