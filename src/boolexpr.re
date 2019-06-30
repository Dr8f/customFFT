open Util;

open Intexpr;

type boolexpr =
  | IsPrime(intexpr)
  | And(list(boolexpr))
  | Equal(intexpr, intexpr)
  | True
  | False
  | Not(boolexpr);

let rec string_of_boolexpr = (e: boolexpr): string =>
  switch (e) {
  | IsPrime(l) => "IsPrime(" ++ string_of_intexpr(l) ++ ")"
  | And(l) =>
    optional_short_infix_list_print("And", " && ", l, string_of_boolexpr)
  | Equal(a, b) =>
    optional_short_print(
      "(" ++ string_of_intexpr(a) ++ " == " ++ string_of_intexpr(b) ++ ")",
      "Equal(" ++ string_of_intexpr(a) ++ ", " ++ string_of_intexpr(b) ++ ")",
    )
  | Not(b) =>
    optional_short_print(
      "!" ++ string_of_boolexpr(b),
      "Not(" ++ string_of_boolexpr(b) ++ ")",
    )
  | True => "True"
  | False => "False"
  };

let meta_collect_boolexpr_on_boolexpr =
    (f: boolexpr => list('a)): (boolexpr => list('a)) => {
  let z = (g: boolexpr => list('a), e: boolexpr): list('a) =>
    switch (e) {
    | And(l) => List.flatten(List.map(g, l))
    | Not(b) => g(b)
    | _ => []
    };

  recursion_collect(z, f);
};

let meta_collect_intexpr_on_boolexpr =
    (f: intexpr => list('a)): (boolexpr => list('a)) =>
  meta_collect_boolexpr_on_boolexpr(
    fun
    | IsPrime(x) => f(x)
    | Equal(a, b) => f(a) @ f(b)
    | _ => [],
  );

let meta_iter_intexpr_on_boolexpr = (f: intexpr => unit): (boolexpr => unit) =>
  (e: boolexpr) =>
    ignore(
      meta_collect_intexpr_on_boolexpr(
        (e: intexpr) => {
          f(e);
          [];
        },
        e,
      ),
    );
