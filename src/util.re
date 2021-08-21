module StringMap = Map.Make(String);

module IntMap =
  Map.Make({
    type t = int;
    let compare = compare;
  });

module IntSet =
  Set.Make({
    let compare = Stdlib.compare;
    type t = int;
  });

let rec white = (n: int): string =>
  if (n <= 0) {
    "";
  } else {
    " " ++ white(n - 1);
  };

let rec range = (i, j) =>
  if (i > j) {
    [];
  } else {
    [i, ...range(i + 1, j)];
  };

let rec last =
  fun
  | [] => None
  | [x] => Some(x)
  | [_, ...t] => last(t);

let drop_last = (l: list('a)) =>
  switch (List.rev(l)) {
  | [] => failwith("could not be inverted, was empty")
  | [_, ...t] => List.rev(t)
  };

/*********************************************
 	 RECURSION SUPPORT
 *********************************************/

type recursion_direction =
  | BottomUp
  | TopDown;

let recursion_transform =
    (
      recursion_direction: recursion_direction,
      z: ('a => 'a, 'a) => 'a,
      f: 'a => 'a,
    )
    : ('a => 'a) => {
  let rec g = (e: 'a): 'a => {
    let s = z(g);
    switch (recursion_direction) {
    | BottomUp => f(s(e))
    | TopDown => s(f(e))
    };
  };
  g;
};

let recursion_transform_ctx =
    (
      recursion_direction: recursion_direction,
      z: ('a => 'a, list('a), 'a) => 'a,
      f: (list('a), 'a) => 'a,
    )
    : ('a => 'a) => {
  let rec g = (ctx: list('a), e: 'a): 'a => {
    let s = z(a => g([e, ...ctx], a), ctx);
    switch (recursion_direction) {
    | BottomUp => f(ctx, s(e))
    | TopDown => s(f(ctx, e))
    };
  };
  g([]);
};

let recursion_collect =
    (z: ('a => list('b), 'a) => list('b), f: 'a => list('b))
    : ('a => list('b)) => {
  let rec g = (e: 'a): list('b) => f(e) @ z(g, e);

  g;
};

let recursion_collect_ctx =
    (
      z: ('a => list('b), list('a), 'a) => list('b),
      f: (list('a), 'a) => list('b),
    )
    : ('a => list('b)) => {
  let rec g = (ctx: list('a), e: 'a): list('b) => {
    let s = z(a => g([e, ...ctx], a), ctx);
    f(ctx, e) @ s(e);
  };

  g([]);
};

/*********************************************
 	 PRINTING
 *********************************************/
let optional_short_print = (short: string, long: string): string => {
  let short_print = true;
  if (short_print) {short} else {long};
};

let optional_short_infix_list_print =
    (name: string, infix: string, l: list('a), f: 'a => string) =>
  optional_short_print(
    String.concat(infix, List.map(f, l)),
    name ++ "([" ++ String.concat("; ", List.map(f, l)) ++ "])",
  );

/*********************************************
 	 APPLYING RULES
 *********************************************/

let rec apply_rewriting_rules = (rules: StringMap.t('a => 'a), e: 'a): 'a => {
  let apply_rewriting_rules_once = (e: 'a): 'a => {
    let f = (_: string, rule: 'a => 'a, e: 'a): 'a =>
      /*      if (e <> outcome) then print_endline ("===  " ^ name ^ "  ===\n    " ^ (string_of_'a e) ^ "\n    " ^ (string_of_spl outcome) ^ "\n") ;  */
      rule(e);

    StringMap.fold(f, rules, e);
  };

  let next = apply_rewriting_rules_once(e);
  if (e == next) {
    e;
  } else {
    apply_rewriting_rules(rules, next);
  };
};
