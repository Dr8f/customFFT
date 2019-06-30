exception AlgoNotApplicable(string);

open Util;

open Spl;

open Intexpr;

open Boolexpr;

let gen_freedom_var = {
  as _;
  val tbl = ref(0);
  pub get = (): intexpr => {
    tbl := tbl^ + 1;
    IFreedom(tbl^);
  }
};

let within_GT_rank_one = (l: list(spl)): bool => {
  print_string(
    "ctx: " ++ String.concat(" ||| ", List.map(Spl.string_of_spl, l)) ++ "\n",
  );
  let mylist = List.flatten(List.map(collect_GT, l));
  let n = List.length(mylist);
  if (n == 0) {
    true;
  } else if (n == 1) {
    switch (List.hd(mylist)) {
    | GT(_, _, _, l) => List.length(l) <= 1
    | _ => assert(false)
    };
  } else {
    false;
  };
};

let algo_cooley_tukey: spl => (boolexpr, list((intexpr, intexpr)), spl) = (
  fun
  | (e: spl) => {
      let conditions = ref([]);
      let freedoms = ref([]);
      let g = (ctx: list(spl), s: spl): spl =>
        switch (s) {
        | DFT(n) when within_GT_rank_one(ctx) =>
          conditions := [Not(IsPrime(n)), ...conditions^];
          let k = gen_freedom_var#get();
          freedoms := [(k, IDivisor(n)), ...freedoms^];
          let m = IDivPerfect(n, k);
          Compose([
            Tensor([DFT(k), I(m)]),
            T(n, m),
            Tensor([I(k), DFT(m)]),
            L(n, k),
          ]);
        | DFT(_) =>
          raise(AlgoNotApplicable("Cooley Tukey not applicable within GT"))
        | x => x
        };

      let f = meta_transform_ctx_spl_on_spl(BottomUp, g);
      (And(conditions^), freedoms^, f(e));
    }:
    spl => (boolexpr, list((intexpr, intexpr)), spl)
);

/* this is for debug only */
let algo_dft_itself: spl => (boolexpr, list((intexpr, intexpr)), spl) = (
  fun
  | (e: spl) => {
      let f =
        meta_transform_spl_on_spl(
          BottomUp,
          fun
          | DFT(n) => DFT(n)
          | x => x,
        );
      (True, [], f(e));
    }:
    spl => (boolexpr, list((intexpr, intexpr)), spl)
);

let algo_dft_base: spl => (boolexpr, list((intexpr, intexpr)), spl) = (
  fun
  | (e: spl) => {
      let conditions = ref([]);
      let f =
        meta_transform_spl_on_spl(
          BottomUp,
          fun
          | DFT(n) => {
              conditions :=
                [Equal(n, IConstant(2)), ...conditions^];
              BB(F(2));
            }

          | Spl.GT(_, _, _, l) as e =>
            if (List.length(l) > 1) {
              raise(
                AlgoNotApplicable(
                  "Cannot apply a base case where there is a rank 2 or more GT, all freedoms have not been resolved",
                ),
              );
            } else {
              e;
            }

          | x => x,
        );
      (And(conditions^), [], f(e));
    }:
    spl => (boolexpr, list((intexpr, intexpr)), spl)
  /* (\* GT rank 1 downrank, should later be part of all base cases *\) */
  /* | Spl.GT(a, g, s, v::[]) ->  */
  /* 	let i = Intexpr.gen_loop_counter#get () in  */
  /* 	ISum(i, v, Compose([S(Idxfunc.FDown(s, i, 0));Spl.Down(a, i, 0);G(Idxfunc.FDown(g, i, 0))])) */
);
