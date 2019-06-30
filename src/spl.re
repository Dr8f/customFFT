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
  | T(n, m) =>
    "T(" ++ string_of_intexpr(n) ++ "," ++ string_of_intexpr(m) ++ ")"
  | L(n, m) =>
    "L(" ++ string_of_intexpr(n) ++ "," ++ string_of_intexpr(m) ++ ")"
  | Compose(list) =>
    optional_short_infix_list_print("Compose", " . ", list, string_of_spl)
  | S(f) => "S(" ++ string_of_idxfunc(f) ++ ")"
  | G(f) => "G(" ++ string_of_idxfunc(f) ++ ")"
  | Diag(f) => "Diag(" ++ string_of_idxfunc(f) ++ ")"
  | DiagData(f, g) =>
    "DiagData("
    ++ string_of_idxfunc(f)
    ++ ", "
    ++ string_of_idxfunc(g)
    ++ ")"
  | ISum(i, high, spl) =>
    "ISum("
    ++ string_of_intexpr(i)
    ++ ","
    ++ string_of_intexpr(high)
    ++ ","
    ++ string_of_spl(spl)
    ++ ")"
  | RS(spl) => "RS(" ++ string_of_spl(spl) ++ ")"
  | UnpartitionnedCall(f, map, funcs, r, d) =>
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
  | PartitionnedCall(childcount, f, cold, reinit, hot, funcs, r, d) =>
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
  | Construct(childcount, f, cold, funcs) =>
    "Construct("
    ++ string_of_int(childcount)
    ++ ", \""
    ++ f
    ++ "\", ["
    ++ String.concat(";", List.map(string_of_intexpr, cold))
    ++ "], ["
    ++ String.concat(";", List.map(string_of_idxfunc, funcs))
    ++ "])"
  | ISumReinitConstruct(childcount, i, high, f, cold, reinit, funcs) =>
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
  | Compute(childcount, f, hot, _, _) =>
    "Compute("
    ++ string_of_int(childcount)
    ++ ", "
    ++ f
    ++ ", ["
    ++ String.concat(";", List.map(string_of_intexpr, hot))
    ++ "])"
  | ISumReinitCompute(childcount, i, high, f, hot, _, _) =>
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
  | GT(a, g, s, l) =>
    "GT("
    ++ string_of_spl(a)
    ++ ", "
    ++ string_of_idxfunc(g)
    ++ ", "
    ++ string_of_idxfunc(s)
    ++ ", ["
    ++ String.concat(";", List.map(string_of_intexpr, l))
    ++ "])"
  | Down(s, l, d) =>
    "Down("
    ++ string_of_spl(s)
    ++ ", "
    ++ string_of_intexpr(l)
    ++ ", "
    ++ string_of_int(d)
    ++ ")"
  | SideArg(s, f) =>
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
    | ISum(v, c, a) => ISum(v, c, g(a))
    | RS(l) => RS(g(l))
    | BB(l) => BB(g(l))
    | GT(a, c, s, l) =>
      GT(g(a), c, s, l)
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
    | Down(s, a, b) => Down(g(s), a, b)
    | SideArg(s, f) => SideArg(g(s), f)
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
    | DiagData(a, b) =>
      DiagData(g(a), g(b))
    | GT(a, c, s, l) =>
      GT(a, g(c), g(s), l)
    | (
        DFT(_) | RS(_) | I(_) | Tensor(_) | T(_) | L(_) | Compose(_) | ISum(_) |
        F(_) |
        BB(_) |
        Down(_) |
        Compute(_) |
        ISumReinitCompute(_)
      ) as e => e
    | Construct(a, b, c, d) =>
      Construct(a, b, c, List.map(g, d))
    | ISumReinitConstruct(a, b, c, d, ee, f, gg) =>
      ISumReinitConstruct(a, b, c, d, ee, f, List.map(g, gg))
    | SideArg(s, f) => SideArg(s, g(f))
    | UnpartitionnedCall(a, b, c, d, e) =>
      UnpartitionnedCall(a, b, List.map(g, c), d, e)
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
    | ISum(v, c, a) =>
      ISum(g(v), g(c), a)
    | GT(v, c, s, l) =>
      GT(v, c, s, List.map(g, l))
    | L(n, m) => L(g(n), g(m))
    | T(n, m) => T(g(n), g(m))
    | I(n) => I(g(n))
    | DFT(n) => DFT(g(n))
    | BB(_) => e
    | UnpartitionnedCall(_) => e
    | PartitionnedCall(_) => e
    | F(_) => e
    | ISumReinitConstruct(a, b, c, d, ee, f, gg) =>
      ISumReinitConstruct(
        a,
        g(b),
        g(c),
        d,
        List.map(g, ee),
        List.map(g, f),
        gg,
      )
    | ISumReinitCompute(a, b, c, d, ee, f, gg) =>
      ISumReinitCompute(a, g(b), g(c), d, List.map(g, ee), g(f), g(gg))
    | Construct(a, b, c, d) =>
      Construct(a, b, List.map(g, c), d)
    | Compute(a, b, c, d, e) =>
      Compute(a, b, List.map(g, c), g(d), g(e))
    | Down(s, l, d) => Down(s, g(l), d)
    | SideArg(_, _) => e
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
    | ISum(_, _, a)
    | GT(a, _, _, _) => g(a)
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
    | DiagData(a, b) => f(ctx, a) @ f(ctx, b)
    | GT(_, a, b, _) => f(ctx, a) @ f(ctx, b)
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
    | ISum(n, m, _)
    | L(n, m)
    | T(n, m) => ff(n) @ ff(m)
    | I(n)
    | DFT(n) => ff(n)
    | GT(_, _, _, l) => List.flatten(List.map(ff, l))
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
  | GT(a, _, _, l) => IMul([spl_range(a), ...l])
  | I(n)
  | T(n, _)
  | L(n, _)
  | DFT(n) => n
  | Compose(list) => spl_range(List.hd(list))
  | S(f) => func_range(f)
  | G(f)
  | Diag(f)
  | DiagData(f, _) => func_domain(f)
  | ISum(_, _, s)
  | RS(s)
  | BB(s) => spl_range(s)
  | F(n) => IConstant(n)
  | ISumReinitCompute(_, _, _, _, _, r, _)
  | Compute(_, _, _, r, _) => r
  | ISumReinitConstruct(_)
  | Construct(_)
  | UnpartitionnedCall(_)
  | PartitionnedCall(_) => assert(false)
  | Down(a, _, _) => spl_range(a)
  | SideArg(a, _) => spl_range(a)
  };

let rec spl_domain = (e: spl): intexpr =>
  switch (e) {
  | F(n) => IConstant(n)
  | Tensor(list) => IMul(List.map(spl_domain, list))
  | GT(a, _, _, l) => IMul([spl_domain(a), ...l])
  | DFT(n)
  | I(n)
  | T(n, _)
  | L(n, _) => n
  | Compose(list) => spl_domain(List.hd(List.rev(list)))
  | S(f) => func_domain(f)
  | G(f) => func_range(f)
  | Diag(f)
  | DiagData(f, _) => func_domain(f) /* by definition a diag range is equal to a diag domain. However the range of the function is larger but noone cares since its precomputed*/
  | ISum(_, _, s)
  | RS(s)
  | BB(s) => spl_domain(s)
  | UnpartitionnedCall(_)
  | PartitionnedCall(_)
  | ISumReinitConstruct(_)
  | Construct(_) => assert(false)
  | ISumReinitCompute(_, _, _, _, _, _, d)
  | Compute(_, _, _, _, d) => d
  | Down(a, _, _) => spl_domain(a)
  | SideArg(a, _) => spl_domain(a)
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
          ISum(
            i,
            k,
            Compose([
              S(
                FH(
                  spl_range(a),
                  IMul([spl_range(a), k]),
                  IMul([spl_range(a), i]),
                  IConstant(1),
                ),
              ),
              a,
              G(
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
          ISum(
            i,
            k,
            Compose([
              S(
                FH(spl_range(a), IMul([spl_range(a), k]), i, k),
              ),
              a,
              G(
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
          GT(
            a,
            FHH(
              spl_domain(a),
              spl_domain(a),
              IConstant(0),
              IConstant(1),
              [spl_domain(a)],
            ),
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
          GT(
            a,
            FHH(
              spl_domain(a),
              spl_domain(a),
              IConstant(0),
              k,
              [IConstant(1)],
            ),
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
      | [GT(a, g, s, v), L(n, k), ...tl] =>
        f([
          GT(a, FCompose([FUp(FL(n, k)), g]), s, v),
          ...tl,
        ])
      | [GT(a, g, s, v), Diag(d), ...tl] =>
        f([
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
      | [ISum(v, c, a), L(n, k), ...tl] =>
        f([
          ISum(v, c, Compose([a, G(FL(n, k))])),
          ...tl,
        ])
      | [ISum(v, c, a), Diag(_) as d, ...tl] =>
        f([ISum(v, c, Compose([a, d])), ...tl])
      | [ISum(v, c, a), G(h), ...tl] =>
        f([ISum(v, c, Compose([a, G(h)])), ...tl])
      | [S(h), ISum(v, c, a), ...tl] =>
        f([ISum(v, c, Compose([S(h), a])), ...tl])
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
    | T(n, k) => Diag(Pre(FD(n, k)))
    | x => x,
  ):
    spl => spl
);

let rule_warp_GT_RS: spl => spl = (
  meta_transform_spl_on_spl(
    BottomUp,
    fun
    | GT(RS(a), g, s, l) =>
      RS(GT(a, g, s, l))
    | GT(Compose([RS(a), RS(b)]), g, s, l) =>
      Compose([
        RS(GT(a, g, s, l)),
        RS(GT(b, g, s, l)),
      ])
    | x => x,
  ):
    spl => spl /*interaction between GT and compose, FIXME opportunity to introduce GTI*/
);

let rule_GT_GT: spl => spl = (
  meta_transform_spl_on_spl(
    BottomUp,
    fun
    | GT(GT(a, ga, sa, la), gb, sb, lb) => {
        let rec f = (elt: idxfunc, count: list('a)): idxfunc =>
          switch (count) {
          | [_, ...tl] => FUp(f(elt, tl))
          | _ => elt
          };

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
    | BB(SideArg(a, f)) => SideArg(a, f)
    | GT(SideArg(a, s), _, _, l) =>
      if (List.length(l) === rank_of_func(s)) {
        SideArg(GT(a, FNil, s, l), FNil);
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
    | Down(Compose(list), j, l) =>
      Compose(List.map(x => Down(x, j, l), list))
    | Down(BB(x), j, l) =>
      BB(Down(x, j, l))
    | Down(F(i), _, _) => F(i)
    | Down(Diag(f), j, l) =>
      Diag(FDown(f, j, l))
    | Down(DiagData(f, g), j, l) =>
      DiagData(
        FDown(f, j, l),
        FDown(g, j, l),
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
      | [F(_), SideArg(a, b), ...tl] =>
        f([SideArg(a, b), ...tl])
      | [SideArg(a, b), G(_), ...tl] =>
        f([SideArg(a, b), ...tl])
      | [S(_), SideArg(a, b), ...tl] =>
        f([SideArg(Compose([S(b), a]), FNil), ...tl])
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
