open Util;

open Intexpr;

open Idxfunc;

type spl =
  | DFT(intexpr)
  | RS(spl) /* Recursion step */
  | Tensor(list(spl))
  | I(intexpr)
  | T(intexpr, intexpr)
  | L(intexpr, intexpr)
  | Compose(list(spl))
  | S(idxfunc)
  | G(idxfunc)
  | Diag(idxfunc) /*multiply diagonal by the content of idxfunc */
  | DiagData(idxfunc, idxfunc) /*first idxfunc is the content of the diag, second idxfunc is the location */
  | ISum(intexpr, intexpr, spl)
  | UnpartitionnedCall(
      string,
      IntMap.t(intexpr),
      list(idxfunc),
      intexpr,
      intexpr,
    )
  | PartitionnedCall(
      int,
      string,
      list(intexpr),
      list(intexpr),
      list(intexpr),
      list(idxfunc),
      intexpr,
      intexpr,
    )
  | Construct(int, string, list(intexpr), list(idxfunc))
  | ISumReinitConstruct(
      int,
      intexpr,
      intexpr,
      string,
      list(intexpr),
      list(intexpr),
      list(idxfunc),
    )
  | Compute(int, string, list(intexpr), intexpr, intexpr)
  | ISumReinitCompute(
      int,
      intexpr,
      intexpr,
      string,
      list(intexpr),
      intexpr,
      intexpr,
    )
  | F(int)
  | BB(spl)
  | GT(spl, idxfunc, idxfunc, list(intexpr))
  | Down(spl, intexpr, int) /*the reason we have a Down in spl is that there are objects such as DiagData that have their own FHH on the side*/
  | SideArg(spl, idxfunc); /*this travels bottom up to see which part of the expression actually need to be PreComputed*/

let rec string_of_spl = (e: spl): string =>
  switch (e) {
  | DFT(n) => "DFT(" ++ string_of_intexpr(n) ++ ")"
  | Tensor(list) =>
    optional_short_infix_list_print("Tensor", " x ", list, string_of_spl)
  | I(n) => "I(" ++ string_of_intexpr(n) ++ ")"
  | [@implicit_arity] T(n, m) =>
    "T(" ++ string_of_intexpr(n) ++ "," ++ string_of_intexpr(m) ++ ")"
  | [@implicit_arity] L(n, m) =>
    "L(" ++ string_of_intexpr(n) ++ "," ++ string_of_intexpr(m) ++ ")"
  | Compose(list) =>
    optional_short_infix_list_print("Compose", " . ", list, string_of_spl)
  | S(f) => "S(" ++ string_of_idxfunc(f) ++ ")"
  | G(f) => "G(" ++ string_of_idxfunc(f) ++ ")"
  | Diag(f) => "Diag(" ++ string_of_idxfunc(f) ++ ")"
  | [@implicit_arity] DiagData(f, g) =>
    "DiagData("
    ++ string_of_idxfunc(f)
    ++ ", "
    ++ string_of_idxfunc(g)
    ++ ")"
  | [@implicit_arity] ISum(i, high, spl) =>
    "ISum("
    ++ string_of_intexpr(i)
    ++ ","
    ++ string_of_intexpr(high)
    ++ ","
    ++ string_of_spl(spl)
    ++ ")"
  | RS(spl) => "RS(" ++ string_of_spl(spl) ++ ")"
  | [@implicit_arity] UnpartitionnedCall(f, map, funcs, r, d) =>
    "UnpartitionnedCall(\""
    ++ f
    ++ "\", ("
    ++ string_of_intexpr_intmap(map)
    ++ "), ["
    ++ String.concat("; ", List.map(string_of_idxfunc, funcs))
    ++ "], "
    ++ string_of_intexpr(r)
    ++ ", "
    ++ string_of_intexpr(d)
    ++ ")"
  | [@implicit_arity]
    PartitionnedCall(childcount, f, cold, reinit, hot, funcs, r, d) =>
    "PartitionnedCall("
    ++ string_of_int(childcount)
    ++ ", \""
    ++ f
    ++ "\", ["
    ++ String.concat(";", List.map(string_of_intexpr, cold))
    ++ "], ["
    ++ String.concat(";", List.map(string_of_intexpr, reinit))
    ++ "], ["
    ++ String.concat(";", List.map(string_of_intexpr, hot))
    ++ "], ["
    ++ String.concat(";", List.map(string_of_idxfunc, funcs))
    ++ "], "
    ++ string_of_intexpr(r)
    ++ ", "
    ++ string_of_intexpr(d)
    ++ ")"
  | [@implicit_arity] Construct(childcount, f, cold, funcs) =>
    "Construct("
    ++ string_of_int(childcount)
    ++ ", \""
    ++ f
    ++ "\", ["
    ++ String.concat(";", List.map(string_of_intexpr, cold))
    ++ "], ["
    ++ String.concat(";", List.map(string_of_idxfunc, funcs))
    ++ "])"
  | [@implicit_arity]
    ISumReinitConstruct(childcount, i, high, f, cold, reinit, funcs) =>
    "ISumReinitConstruct("
    ++ string_of_int(childcount)
    ++ ", "
    ++ string_of_intexpr(i)
    ++ ", "
    ++ string_of_intexpr(high)
    ++ ", \""
    ++ f
    ++ "\", ["
    ++ String.concat(";", List.map(string_of_intexpr, cold))
    ++ "], ["
    ++ String.concat(";", List.map(string_of_intexpr, reinit))
    ++ "], ["
    ++ String.concat(";", List.map(string_of_idxfunc, funcs))
    ++ "])"
  | [@implicit_arity] Compute(childcount, f, hot, _, _) =>
    "Compute("
    ++ string_of_int(childcount)
    ++ ", "
    ++ f
    ++ ", ["
    ++ String.concat(";", List.map(string_of_intexpr, hot))
    ++ "])"
  | [@implicit_arity] ISumReinitCompute(childcount, i, high, f, hot, _, _) =>
    "ISumReinitCompute("
    ++ string_of_int(childcount)
    ++ ", "
    ++ string_of_intexpr(i)
    ++ ", "
    ++ string_of_intexpr(high)
    ++ ", "
    ++ f
    ++ ", ["
    ++ String.concat(";", List.map(string_of_intexpr, hot))
    ++ "])"
  | F(i) => "F(" ++ string_of_int(i) ++ ")"
  | BB(x) => "BB(" ++ string_of_spl(x) ++ ")"
  | [@implicit_arity] GT(a, g, s, l) =>
    "GT("
    ++ string_of_spl(a)
    ++ ", "
    ++ string_of_idxfunc(g)
    ++ ", "
    ++ string_of_idxfunc(s)
    ++ ", ["
    ++ String.concat(";", List.map(string_of_intexpr, l))
    ++ "])"
  | [@implicit_arity] Down(s, l, d) =>
    "Down("
    ++ string_of_spl(s)
    ++ ", "
    ++ string_of_intexpr(l)
    ++ ", "
    ++ string_of_int(d)
    ++ ")"
  | [@implicit_arity] SideArg(s, f) =>
    "SideArg(" ++ string_of_spl(s) ++ ", " ++ string_of_idxfunc(f) ++ ")"
  };

/*********************************************
 	 METARULES
 *********************************************/

let meta_transform_ctx_spl_on_spl =
    (recursion_direction: recursion_direction)
    : (((list(spl), spl) => spl, spl) => spl) => {
  let z = (g: spl => spl, _: list(spl), e: spl): spl =>
    switch (e) {
    | Compose(l) => Compose(List.map(g, l))
    | Tensor(l) => Tensor(List.map(g, l))
    | [@implicit_arity] ISum(v, c, a) => [@implicit_arity] ISum(v, c, g(a))
    | RS(l) => RS(g(l))
    | BB(l) => BB(g(l))
    | [@implicit_arity] GT(a, c, s, l) =>
      [@implicit_arity] GT(g(a), c, s, l)
    | DFT(_)
    | I(_)
    | T(_)
    | L(_)
    | DiagData(_)
    | Diag(_)
    | S(_)
    | G(_)
    | UnpartitionnedCall(_)
    | F(_)
    | ISumReinitCompute(_)
    | Compute(_)
    | ISumReinitConstruct(_)
    | Construct(_)
    | PartitionnedCall(_) => e
    | [@implicit_arity] Down(s, a, b) => [@implicit_arity] Down(g(s), a, b)
    | [@implicit_arity] SideArg(s, f) => [@implicit_arity] SideArg(g(s), f)
    };

  recursion_transform_ctx(recursion_direction, z);
};

let meta_transform_spl_on_spl =
    (recursion_direction: recursion_direction, z: spl => spl): (spl => spl) =>
  meta_transform_ctx_spl_on_spl(recursion_direction, _ => z);

let meta_transform_ctx_idxfunc_on_spl =
    (
      recursion_direction: recursion_direction,
      f: (list(spl), list(idxfunc), idxfunc) => idxfunc,
    )
    : (spl => spl) => {
  /* print_string "meta_transform_ctx_idxfunc_on_spl\n"; */
  let h = (ctx: list(spl), e: spl): spl => {
    let g =
      meta_transform_ctx_idxfunc_on_idxfunc(recursion_direction, f(ctx));
    switch (e) {
    | G(l) => G(g(l))
    | S(l) => S(g(l))
    | Diag(l) => Diag(g(l))
    | [@implicit_arity] DiagData(a, b) =>
      [@implicit_arity] DiagData(g(a), g(b))
    | [@implicit_arity] GT(a, c, s, l) =>
      [@implicit_arity] GT(a, g(c), g(s), l)
    | (
        DFT(_) | RS(_) | I(_) | Tensor(_) | T(_) | L(_) | Compose(_) | ISum(_) |
        F(_) |
        BB(_) |
        Down(_) |
        Compute(_) |
        ISumReinitCompute(_)
      ) as e => e
    | [@implicit_arity] Construct(a, b, c, d) =>
      [@implicit_arity] Construct(a, b, c, List.map(g, d))
    | [@implicit_arity] ISumReinitConstruct(a, b, c, d, ee, f, gg) =>
      [@implicit_arity]
      ISumReinitConstruct(a, b, c, d, ee, f, List.map(g, gg))
    | [@implicit_arity] SideArg(s, f) => [@implicit_arity] SideArg(s, g(f))
    | [@implicit_arity] UnpartitionnedCall(a, b, c, d, e) =>
      [@implicit_arity] UnpartitionnedCall(a, b, List.map(g, c), d, e)
    | e =>
      failwith(
        "meta_transform_idxfunc_on_spl, not handled: " ++ string_of_spl(e),
      )
    };
  };

  meta_transform_ctx_spl_on_spl(recursion_direction, h);
};

let meta_transform_idxfunc_on_spl =
    (recursion_direction: recursion_direction, z: idxfunc => idxfunc)
    : (spl => spl) =>
  meta_transform_ctx_idxfunc_on_spl(recursion_direction, (_, _) => z);

let meta_transform_ctx_intexpr_on_spl =
    (
      recursion_direction: recursion_direction,
      f: (list(spl), list(idxfunc), list(intexpr), intexpr) => intexpr,
    )
    : (spl => spl) => {
  /* print_string "meta_transform_ctx intexpr_on_spl\n"; */
  let h = (ctx: list(spl), e: spl): spl => {
    let g =
      meta_transform_ctx_intexpr_on_intexpr(recursion_direction, f(ctx, []));
    switch (e) {
    | Compose(_)
    | Tensor(_)
    | RS(_)
    | Diag(_)
    | DiagData(_)
    | G(_)
    | S(_) => e
    | [@implicit_arity] ISum(v, c, a) =>
      [@implicit_arity] ISum(g(v), g(c), a)
    | [@implicit_arity] GT(v, c, s, l) =>
      [@implicit_arity] GT(v, c, s, List.map(g, l))
    | [@implicit_arity] L(n, m) => [@implicit_arity] L(g(n), g(m))
    | [@implicit_arity] T(n, m) => [@implicit_arity] T(g(n), g(m))
    | I(n) => I(g(n))
    | DFT(n) => DFT(g(n))
    | BB(_) => e
    | UnpartitionnedCall(_) => e
    | PartitionnedCall(_) => e
    | F(_) => e
    | [@implicit_arity] ISumReinitConstruct(a, b, c, d, ee, f, gg) =>
      [@implicit_arity]
      ISumReinitConstruct(
        a,
        g(b),
        g(c),
        d,
        List.map(g, ee),
        List.map(g, f),
        gg,
      )
    | [@implicit_arity] ISumReinitCompute(a, b, c, d, ee, f, gg) =>
      [@implicit_arity]
      ISumReinitCompute(a, g(b), g(c), d, List.map(g, ee), g(f), g(gg))
    | [@implicit_arity] Construct(a, b, c, d) =>
      [@implicit_arity] Construct(a, b, List.map(g, c), d)
    | [@implicit_arity] Compute(a, b, c, d, e) =>
      [@implicit_arity] Compute(a, b, List.map(g, c), g(d), g(e))
    | [@implicit_arity] Down(s, l, d) => [@implicit_arity] Down(s, g(l), d)
    | [@implicit_arity] SideArg(_, _) => e
    };
  };
  /* | _ -> failwith("meta_transform_intexpr_on_spl, not handled: "^(string_of_spl e))         		 */

  (e: spl) => {
    let z =
        (splctx: list(spl), idxfuncctx: list(idxfunc)): (idxfunc => idxfunc) => {
      let zz = (hh: list(idxfunc)): ((list(intexpr), intexpr) => intexpr) =>
        f(splctx, idxfuncctx @ hh);
      meta_transform_ctx_intexpr_on_idxfunc(recursion_direction, zz);
    };

    let res = meta_transform_ctx_idxfunc_on_spl(recursion_direction, z, e);
    (meta_transform_ctx_spl_on_spl(recursion_direction, h))(res);
  };
};

let meta_transform_intexpr_on_spl =
    (recursion_direction: recursion_direction, z: intexpr => intexpr)
    : (spl => spl) =>
  meta_transform_ctx_intexpr_on_spl(recursion_direction, (_, _, _) => z);

let meta_collect_ctx_spl_on_spl =
    (f: (list(spl), spl) => list('a)): (spl => list('a)) => {
  let z = (g: spl => list('a), _: list(spl), e: spl): list('a) =>
    switch (e) {
    | Compose(l)
    | Tensor(l) => List.flatten(List.map(g, l))
    | [@implicit_arity] ISum(_, _, a)
    | [@implicit_arity] GT(a, _, _, _) => g(a)
    | RS(a) => g(a)
    | _ => []
    };

  recursion_collect_ctx(z, f);
};

let meta_collect_spl_on_spl = (z: spl => list('a)): (spl => list('a)) =>
  meta_collect_ctx_spl_on_spl(_ => z);

let meta_collect_ctx_idxfunc_on_spl =
    (f: (list(spl), idxfunc) => list('a)): (spl => list('a)) => {
  let z = (ctx: list(spl), e: spl): list('a) =>
    switch (e) {
    | G(l) => f(ctx, l)
    | S(l) => f(ctx, l)
    | Diag(l) => f(ctx, l)
    | [@implicit_arity] DiagData(a, b) => f(ctx, a) @ f(ctx, b)
    | [@implicit_arity] GT(_, a, b, _) => f(ctx, a) @ f(ctx, b)
    | _ => []
    };

  meta_collect_ctx_spl_on_spl(z);
};

let meta_collect_idxfunc_on_spl =
    (z: idxfunc => list('a)): (spl => list('a)) =>
  meta_collect_ctx_idxfunc_on_spl(_ => z);

let meta_collect_intexpr_on_spl =
    (f: intexpr => list('a)): (spl => list('a)) => {
  let direct_from_spl = (ff: intexpr => list('a), e: spl): list('a) =>
    switch (e) {
    | Compose(_)
    | Tensor(_)
    | RS(_)
    | Diag(_)
    | DiagData(_)
    | G(_)
    | S(_)
    | UnpartitionnedCall(_)
    | PartitionnedCall(_) => []
    | [@implicit_arity] ISum(n, m, _)
    | [@implicit_arity] L(n, m)
    | [@implicit_arity] T(n, m) => ff(n) @ ff(m)
    | I(n)
    | DFT(n) => ff(n)
    | [@implicit_arity] GT(_, _, _, l) => List.flatten(List.map(ff, l))
    | ISumReinitCompute(_)
    | Compute(_)
    | ISumReinitConstruct(_)
    | Construct(_) => assert(false)
    | _ =>
      failwith(
        "meta_collect_intexpr_on_spl, not handled: " ++ string_of_spl(e),
      )
    };

  (e: spl) => {
    let ff = meta_collect_intexpr_on_intexpr(f);
    (meta_collect_spl_on_spl(direct_from_spl(ff)))(e)
    @ (meta_collect_idxfunc_on_spl(meta_collect_intexpr_on_idxfunc(ff)))(e);
  };
};

let meta_iter_ctx_spl_on_spl = (f: (list(spl), spl) => unit): (spl => unit) =>
  (e: spl) =>
    ignore(
      (
        meta_collect_ctx_spl_on_spl((ctx: list(spl), e: spl) => {
          f(ctx, e);
          [];
        })
      )(
        e,
      ),
    );

let meta_iter_spl_on_spl = (z: spl => unit): (spl => unit) =>
  meta_iter_ctx_spl_on_spl(_ => z);

let meta_iter_ctx_idxfunc_on_spl =
    (f: (list(spl), idxfunc) => unit): (spl => unit) =>
  (e: spl) =>
    ignore(
      (
        meta_collect_ctx_idxfunc_on_spl((ctx: list(spl), e: idxfunc) => {
          f(ctx, e);
          [];
        })
      )(
        e,
      ),
    );

let meta_iter_idxfunc_on_spl = (f: idxfunc => unit): (spl => unit) =>
  meta_iter_ctx_idxfunc_on_spl(_ => f);

let meta_iter_intexpr_on_spl = (f: intexpr => unit): (spl => unit) =>
  (e: spl) =>
    ignore(
      meta_collect_intexpr_on_spl(
        (e: intexpr) => {
          f(e);
          [];
        },
        e,
      ),
    );

let meta_compose_spl =
    (recursion_direction: recursion_direction, f: list(spl) => list(spl))
    : (spl => spl) =>
  meta_transform_spl_on_spl(
    recursion_direction,
    fun
    | Compose(l) => Compose(f(l))
    | x => x,
  );

let meta_tensorize_spl =
    (recursion_direction: recursion_direction, f: list(spl) => list(spl))
    : (spl => spl) =>
  meta_transform_spl_on_spl(
    recursion_direction,
    fun
    | Tensor(l) => Tensor(f(l))
    | x => x,
  );

let collect_GT: spl => list(spl) = (
  meta_collect_spl_on_spl(
    fun
    | GT(_) as x => [x]
    | _ => [],
  ):
    spl => list(spl)
);

/*********************************************
 	 RANGE AND DOMAIN
 *********************************************/
let rec spl_range = (e: spl): intexpr =>
  switch (e) {
  | Tensor(list) => IMul(List.map(spl_range, list))
  | [@implicit_arity] GT(a, _, _, l) => IMul([spl_range(a), ...l])
  | I(n)
  | [@implicit_arity] T(n, _)
  | [@implicit_arity] L(n, _)
  | DFT(n) => n
  | Compose(list) => spl_range(List.hd(list))
  | S(f) => func_range(f)
  | G(f)
  | Diag(f)
  | [@implicit_arity] DiagData(f, _) => func_domain(f)
  | [@implicit_arity] ISum(_, _, s)
  | RS(s)
  | BB(s) => spl_range(s)
  | F(n) => IConstant(n)
  | [@implicit_arity] ISumReinitCompute(_, _, _, _, _, r, _)
  | [@implicit_arity] Compute(_, _, _, r, _) => r
  | ISumReinitConstruct(_)
  | Construct(_)
  | UnpartitionnedCall(_)
  | PartitionnedCall(_) => assert(false)
  | [@implicit_arity] Down(a, _, _) => spl_range(a)
  | [@implicit_arity] SideArg(a, _) => spl_range(a)
  };

let rec spl_domain = (e: spl): intexpr =>
  switch (e) {
  | F(n) => IConstant(n)
  | Tensor(list) => IMul(List.map(spl_domain, list))
  | [@implicit_arity] GT(a, _, _, l) => IMul([spl_domain(a), ...l])
  | DFT(n)
  | I(n)
  | [@implicit_arity] T(n, _)
  | [@implicit_arity] L(n, _) => n
  | Compose(list) => spl_domain(List.hd(List.rev(list)))
  | S(f) => func_domain(f)
  | G(f) => func_range(f)
  | Diag(f)
  | [@implicit_arity] DiagData(f, _) => func_domain(f) /* by definition a diag range is equal to a diag domain. However the range of the function is larger but noone cares since its precomputed*/
  | [@implicit_arity] ISum(_, _, s)
  | RS(s)
  | BB(s) => spl_domain(s)
  | UnpartitionnedCall(_)
  | PartitionnedCall(_)
  | ISumReinitConstruct(_)
  | Construct(_) => assert(false)
  | [@implicit_arity] ISumReinitCompute(_, _, _, _, _, _, d)
  | [@implicit_arity] Compute(_, _, _, _, d) => d
  | [@implicit_arity] Down(a, _, _) => spl_domain(a)
  | [@implicit_arity] SideArg(a, _) => spl_domain(a)
  };

/*********************************************
 	 SPL RULES
 *********************************************/

let rule_tensor_to_isum: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [I(k), a, ...tl] =>
        let i = gen_loop_counter#get();
        f([
          [@implicit_arity]
          ISum(
            i,
            k,
            Compose([
              S(
                [@implicit_arity]
                FH(
                  spl_range(a),
                  IMul([spl_range(a), k]),
                  IMul([spl_range(a), i]),
                  IConstant(1),
                ),
              ),
              a,
              G(
                [@implicit_arity]
                FH(
                  spl_domain(a),
                  IMul([spl_domain(a), k]),
                  IMul([spl_domain(a), i]),
                  IConstant(1),
                ),
              ),
            ]),
          ),
          ...tl,
        ]);
      | [a, I(k), ...tl] =>
        let i = gen_loop_counter#get();
        f([
          [@implicit_arity]
          ISum(
            i,
            k,
            Compose([
              S(
                [@implicit_arity]
                FH(spl_range(a), IMul([spl_range(a), k]), i, k),
              ),
              a,
              G(
                [@implicit_arity]
                FH(spl_domain(a), IMul([spl_domain(a), k]), i, k),
              ),
            ]),
          ),
          ...tl,
        ]);
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_tensorize_spl(BottomUp, f);
  }:
    spl => spl
);

let rule_tensor_to_GT: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [I(k), a, ...tl] => [
          [@implicit_arity]
          GT(
            a,
            [@implicit_arity]
            FHH(
              spl_domain(a),
              spl_domain(a),
              IConstant(0),
              IConstant(1),
              [spl_domain(a)],
            ),
            [@implicit_arity]
            FHH(
              spl_range(a),
              spl_range(a),
              IConstant(0),
              IConstant(1),
              [spl_range(a)],
            ),
            [k],
          ),
          ...tl,
        ]
      | [a, I(k), ...tl] => [
          [@implicit_arity]
          GT(
            a,
            [@implicit_arity]
            FHH(
              spl_domain(a),
              spl_domain(a),
              IConstant(0),
              k,
              [IConstant(1)],
            ),
            [@implicit_arity]
            FHH(
              spl_range(a),
              spl_range(a),
              IConstant(0),
              k,
              [IConstant(1)],
            ),
            [k],
          ),
          ...tl,
        ]
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_tensorize_spl(BottomUp, f);
  }:
    spl => spl
);

let rule_suck_inside_GT: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [[@implicit_arity] GT(a, g, s, v), [@implicit_arity] L(n, k), ...tl] =>
        f([
          [@implicit_arity]
          GT(a, FCompose([FUp([@implicit_arity] FL(n, k)), g]), s, v),
          ...tl,
        ])
      | [[@implicit_arity] GT(a, g, s, v), Diag(d), ...tl] =>
        f([
          [@implicit_arity]
          GT(Compose([a, Diag(FCompose([FUp(d), g]))]), g, s, v),
          ...tl,
        ])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_spl(BottomUp, f);
  }:
    spl => spl
);

/* YSV thesis 2.44 */
let rule_suck_inside_isum: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [[@implicit_arity] ISum(v, c, a), [@implicit_arity] L(n, k), ...tl] =>
        f([
          [@implicit_arity]
          ISum(v, c, Compose([a, G([@implicit_arity] FL(n, k))])),
          ...tl,
        ])
      | [[@implicit_arity] ISum(v, c, a), Diag(_) as d, ...tl] =>
        f([[@implicit_arity] ISum(v, c, Compose([a, d])), ...tl])
      | [[@implicit_arity] ISum(v, c, a), G(h), ...tl] =>
        f([[@implicit_arity] ISum(v, c, Compose([a, G(h)])), ...tl])
      | [S(h), [@implicit_arity] ISum(v, c, a), ...tl] =>
        f([[@implicit_arity] ISum(v, c, Compose([S(h), a])), ...tl])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_spl(BottomUp, f);
  }:
    spl => spl
);

let rule_transorm_T_into_diag: spl => spl = (
  meta_transform_spl_on_spl(
    BottomUp,
    fun
    | [@implicit_arity] T(n, k) => Diag(Pre([@implicit_arity] FD(n, k)))
    | x => x,
  ):
    spl => spl
);

let rule_warp_GT_RS: spl => spl = (
  meta_transform_spl_on_spl(
    BottomUp,
    fun
    | [@implicit_arity] GT(RS(a), g, s, l) =>
      RS([@implicit_arity] GT(a, g, s, l))
    | [@implicit_arity] GT(Compose([RS(a), RS(b)]), g, s, l) =>
      Compose([
        RS([@implicit_arity] GT(a, g, s, l)),
        RS([@implicit_arity] GT(b, g, s, l)),
      ])
    | x => x,
  ):
    spl => spl /*interaction between GT and compose, FIXME opportunity to introduce GTI*/
);

let rule_GT_GT: spl => spl = (
  meta_transform_spl_on_spl(
    BottomUp,
    fun
    | [@implicit_arity] GT([@implicit_arity] GT(a, ga, sa, la), gb, sb, lb) => {
        let rec f = (elt: idxfunc, count: list('a)): idxfunc =>
          switch (count) {
          | [_, ...tl] => FUp(f(elt, tl))
          | _ => elt
          };

        [@implicit_arity]
        GT(
          a,
          FCompose([f(gb, la), ga]),
          FCompose([sa, f(sb, la)]),
          la @ lb,
        );
      }
    | x => x,
  ):
    spl => spl /*FIXME check me*/
  /* print_string("\n\nGT_GT!!\n\n:"^(string_of_spl e)^"\n"); */
);

let rule_pull_side_argument: spl => spl = (
  meta_transform_spl_on_spl(
    BottomUp,
    fun
    | BB([@implicit_arity] SideArg(a, f)) => [@implicit_arity] SideArg(a, f)
    | [@implicit_arity] GT([@implicit_arity] SideArg(a, s), _, _, l) =>
      if (List.length(l) === rank_of_func(s)) {
        [@implicit_arity] SideArg([@implicit_arity] GT(a, FNil, s, l), FNil);
      } else {
        failwith("not implemented yet here");
      }
    | x => x,
  ):
    spl => spl
);

let rule_suck_inside_RS: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [RS(a), Diag(_) as b, ...tl] => f([RS(Compose([a, b])), ...tl])
      | [RS(a), G(_) as b, ...tl] => f([RS(Compose([a, b])), ...tl])
      | [RS(a), L(_) as b, ...tl] => f([RS(Compose([a, b])), ...tl])
      | [S(_) as a, RS(b), ...tl] => f([RS(Compose([a, b])), ...tl])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_spl(BottomUp, f);
  }:
    spl => spl
);

let rule_remove_unary_compose: spl => spl = (
  meta_transform_spl_on_spl(
    BottomUp,
    fun
    | Compose([a]) => a
    | x => x,
  ):
    spl => spl
);

let rule_remove_unary_tensor: spl => spl = (
  meta_transform_spl_on_spl(
    BottomUp,
    fun
    | Tensor([a]) => a
    | x => x,
  ):
    spl => spl
);

let rule_distribute_downrank_spl: spl => spl = (
  meta_transform_spl_on_spl(
    TopDown,
    fun
    | [@implicit_arity] Down(Compose(list), j, l) =>
      Compose(List.map(x => [@implicit_arity] Down(x, j, l), list))
    | [@implicit_arity] Down(BB(x), j, l) =>
      BB([@implicit_arity] Down(x, j, l))
    | [@implicit_arity] Down(F(i), _, _) => F(i)
    | [@implicit_arity] Down(Diag(f), j, l) =>
      Diag([@implicit_arity] FDown(f, j, l))
    | [@implicit_arity] Down([@implicit_arity] DiagData(f, g), j, l) =>
      [@implicit_arity]
      DiagData(
        [@implicit_arity] FDown(f, j, l),
        [@implicit_arity] FDown(g, j, l),
      )
    | x => x,
  ):
    spl => spl
);

let rule_flatten_compose: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [Compose(a), ...tl] => f(a @ tl)
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_spl(BottomUp, f);
  }:
    spl => spl
);

let rule_pull_sidearg_thru_compose: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [F(_), [@implicit_arity] SideArg(a, b), ...tl] =>
        f([[@implicit_arity] SideArg(a, b), ...tl])
      | [[@implicit_arity] SideArg(a, b), G(_), ...tl] =>
        f([[@implicit_arity] SideArg(a, b), ...tl])
      | [S(_), [@implicit_arity] SideArg(a, b), ...tl] =>
        f([[@implicit_arity] SideArg(Compose([S(b), a]), FNil), ...tl])
      | [a, G(FNil), ...tl] => f([a, ...tl])
      | [a, b, ...tl] => [a, ...f([b, ...tl])]
      | x => x
      };

    meta_compose_spl(BottomUp, f);
  }:
    spl => spl
);

let rule_compose_gather_gather: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [G(a), G(b), ...tl] => f([G(FCompose([b, a])), ...tl])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_spl(BottomUp, f);
  }:
    spl => spl
);

let rule_compose_scatter_scatter: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [S(a), S(b), ...tl] => f([S(FCompose([a, b])), ...tl])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_spl(BottomUp, f);
  }:
    spl => spl
);

let rule_compose_gather_diag: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [G(a), Diag(b), ...tl] => f([Diag(FCompose([b, a])), G(a), ...tl])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_spl(BottomUp, f);
  }:
    spl => spl
);

let rule_compose_BB_diag: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [BB(spl), Diag(b), ...tl] => [BB(Compose([spl, Diag(b)])), ...tl]
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_spl(BottomUp, f);
  }:
    spl => spl
);

let rule_compose_BB_gather: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [BB(spl), G(b), ...tl] => [BB(Compose([spl, G(b)])), ...tl]
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_spl(BottomUp, f);
  }:
    spl => spl
);

let rule_compose_scatter_BB: spl => spl = (
  {
    let rec f = (l: list(spl)): list(spl) =>
      switch (l) {
      | [S(b), BB(spl), ...tl] => [BB(Compose([S(b), spl])), ...tl]
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_spl(BottomUp, f);
  }:
    spl => spl
);

let spl_rulemap =
  List.fold_left(
    (map, (name, rule)) => StringMap.add(name, rule, map),
    StringMap.empty,
    [
      /* ("Tensor to ISum", rule_tensor_to_isum); */
      ("Remove unary tensor", rule_remove_unary_tensor),
      ("Remove unary compose", rule_remove_unary_compose),
      ("Transform T into diag", rule_transorm_T_into_diag),
      ("Suck inside ISum", rule_suck_inside_isum),
      ("Suck inside RS", rule_suck_inside_RS),
      ("Flatten Compose", rule_flatten_compose),
      ("Compose Gather Gather", rule_compose_gather_gather),
      ("Compose Scatter Scatter", rule_compose_scatter_scatter),
      ("Compose Gather Diag", rule_compose_gather_diag),
      ("Compose BB Diag", rule_compose_BB_diag),
      ("Compose BB Gather", rule_compose_BB_gather),
      ("Compose Scatter BB", rule_compose_scatter_BB),
      ("Distribute FDown", rule_distribute_downrank_spl),
      ("Rule Pull Side Argument", rule_pull_side_argument),
      (
        "Rule Pull Side Argument Thru Compose",
        rule_pull_sidearg_thru_compose,
      ),
      ("rule_GT_GT", rule_GT_GT),
      /* TODO
           Currently breaks because DFT is applied within GT
           Should introduce GT downrank to verify that RS4 and RS 5 (page 88) are properly generated and that the all code runs
           Then introduce DFT within GT to breakdown the rest
         */
      ("Tensor to GT", rule_tensor_to_GT),
      ("rule_suck_inside_GT", rule_suck_inside_GT),
      ("rule_warp_GT_RS", rule_warp_GT_RS),
    ]
    @ List.map(
        ((name, rule)) =>
          ("Lifted " ++ name, meta_transform_intexpr_on_spl(BottomUp, rule)),
        StringMap.bindings(intexpr_rulemap),
      )
    @ List.map(
        ((name, rule)) =>
          ("Lifted " ++ name, meta_transform_idxfunc_on_spl(BottomUp, rule)),
        StringMap.bindings(idxfunc_rulemap),
      ),
  );

let simplify_spl = (f: spl): spl => apply_rewriting_rules(spl_rulemap, f);
