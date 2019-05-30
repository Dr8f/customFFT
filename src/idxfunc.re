open Util;

open Ctype;

open Intexpr;

type idxfunc =
  | FH(intexpr, intexpr, intexpr, intexpr)
  /* FH(domain, range, base, stride) maps I(src) to I(dest) so that FH(d,r,b,s)(i) = b + i*s */
  | FL(intexpr, intexpr)
  | FD(intexpr, intexpr)
  /* FD(n,k) maps I(n) to a diag of w(n, - 0*0) ... w(n, - (k-1)*0) w(n, - 0*1) ... w(n, - (k-1)*1) ... ... w(n, - (k-1) * (n/k-1)) where w(n, x) = exp(2 Pi * I * x /n) */
  /* thus FD(n,k)(i) = w(n, -(i mod k) * (i\k)) */
  | FCompose(list(idxfunc))
  | Pre(idxfunc) /* Precompute */
  | PreWrap(cvar, list(intexpr), list(idxfunc), intexpr) /*domain*/
  | FArg(cvar, list(intexpr)) /*domain*/ /*FIXME: Do we still need FArg to have a intexpr *list* ?*/
  | FHH(intexpr, intexpr, intexpr, intexpr, list(intexpr))
  /* FHH(domain, range, base, stride0, vector strides) maps Z**k x I(str) to I(dest) so FHH(d,r,b,s,vs)(j_k .. j_1, i) = b + i*s + Sum j_k * vs_k*/
  | FUp(idxfunc)
  | FDown(idxfunc, intexpr, int)
  | FNil;

let rec string_of_idxfunc = (e: idxfunc): string =>
  switch (e) {
  | [@implicit_arity] FH(src, dest, j, k) =>
    "FH("
    ++ string_of_intexpr(src)
    ++ ","
    ++ string_of_intexpr(dest)
    ++ ","
    ++ string_of_intexpr(j)
    ++ ","
    ++ string_of_intexpr(k)
    ++ ")"
  | [@implicit_arity] FL(j, k) =>
    "FL(" ++ string_of_intexpr(j) ++ ", " ++ string_of_intexpr(k) ++ ")"
  | [@implicit_arity] FD(n, k) =>
    "FD(" ++ string_of_intexpr(n) ++ ", " ++ string_of_intexpr(k) ++ ")"
  | FCompose(l) =>
    optional_short_infix_list_print("FCompose", " . ", l, string_of_idxfunc)

  | Pre(l) => "Pre(" ++ string_of_idxfunc(l) ++ ")"
  | FUp(l) => "FUp(" ++ string_of_idxfunc(l) ++ ")"
  | [@implicit_arity] FDown(f, l, d) =>
    "FDown("
    ++ string_of_idxfunc(f)
    ++ ", "
    ++ string_of_intexpr(l)
    ++ ", "
    ++ string_of_int(d)
    ++ ")"
  | [@implicit_arity] PreWrap(cvar, l, funcs, d) =>
    "PreWrap("
    ++ string_of_cvar(cvar)
    ++ ", ["
    ++ String.concat("; ", List.map(string_of_intexpr, l))
    ++ "], ["
    ++ String.concat("; ", List.map(string_of_idxfunc, funcs))
    ++ "], "
    ++ string_of_intexpr(d)
    ++ ")"
  | [@implicit_arity] FArg(cvar, d) =>
    "FArg("
    ++ string_of_cvar(cvar)
    ++ ", ["
    ++ String.concat("; ", List.map(string_of_intexpr, d))
    ++ "])"
  | [@implicit_arity] FHH(d, r, b, s, vs) =>
    "FHH("
    ++ string_of_intexpr(d)
    ++ ", "
    ++ string_of_intexpr(r)
    ++ ", "
    ++ string_of_intexpr(b)
    ++ ", "
    ++ string_of_intexpr(s)
    ++ ", ["
    ++ String.concat("; ", List.map(string_of_intexpr, vs))
    ++ "] )"
  | FNil => "FNil"
  };

let meta_transform_ctx_idxfunc_on_idxfunc =
    (recursion_direction: recursion_direction)
    : (((list(idxfunc), idxfunc) => idxfunc, idxfunc) => idxfunc) => {
  let z = (g: idxfunc => idxfunc, _: list(idxfunc), e: idxfunc): idxfunc =>
    switch (e) {
    | FCompose(l) => FCompose(List.map(g, l))
    | Pre(l) => Pre(g(l))
    | FUp(l) => FUp(g(l))
    | [@implicit_arity] FDown(f, a, b) =>
      [@implicit_arity] FDown(g(f), a, b)
    | [@implicit_arity] PreWrap(cvar, b, c, d) =>
      [@implicit_arity] PreWrap(cvar, b, List.map(g, c), d)
    | FHH(_)
    | FD(_)
    | FH(_)
    | FL(_)
    | FArg(_)
    | FNil => e
    };
  /* | _ -> failwith("meta_transform_idxfunc_on_idxfunc, not handled: "^(string_of_idxfunc e))         		 */

  recursion_transform_ctx(recursion_direction, z);
};

let meta_transform_idxfunc_on_idxfunc =
    (recursion_direction: recursion_direction, z: idxfunc => idxfunc)
    : (idxfunc => idxfunc) =>
  meta_transform_ctx_idxfunc_on_idxfunc(recursion_direction, _ => z);

let meta_transform_ctx_intexpr_on_idxfunc =
    (
      recursion_direction: recursion_direction,
      f: (list(idxfunc), list(intexpr), intexpr) => intexpr,
    )
    : (idxfunc => idxfunc) => {
  /* print_string "meta_transform_ctx_intexpr_on_idxfunc\n"; */
  let h = (ctx: list(idxfunc), e: idxfunc): idxfunc => {
    let g =
      meta_transform_ctx_intexpr_on_intexpr(recursion_direction, f(ctx));
    switch (e) {
    | [@implicit_arity] FH(a, b, c, d) =>
      let ga = g(a);
      let gb = g(b);
      let gc = g(c);
      [@implicit_arity] FH(ga, gb, gc, g(d));
    | [@implicit_arity] FL(a, b) =>
      let ga = g(a);
      [@implicit_arity] FL(ga, g(b));
    | [@implicit_arity] FD(a, b) =>
      let ga = g(a);
      [@implicit_arity] FD(ga, g(b));
    | (FCompose(_) | Pre(_) | FUp(_) | FNil) as e => e
    | [@implicit_arity] PreWrap(cvar, f, funcs, d) =>
      [@implicit_arity] PreWrap(cvar, f, funcs, g(d)) /*FIXME: f is not parameterized because we don't want to parameterize inside the call, should be done with context maybe?*/
    | [@implicit_arity] FArg(cvar, f) =>
      [@implicit_arity] FArg(cvar, List.map(g, f))
    | [@implicit_arity] FDown(f, a, i) =>
      [@implicit_arity] FDown(f, g(a), i)
    | [@implicit_arity] FHH(a, b, c, d, vs) =>
      let ga = g(a);
      let gb = g(b);
      let gc = g(c);
      let gd = g(d);
      [@implicit_arity] FHH(ga, gb, gc, gd, List.map(g, vs));
    };
  };
  /* | _ as e -> failwith("meta_transform_intexpr_on_idxfunc, not handled: "^(string_of_idxfunc e)) */

  meta_transform_ctx_idxfunc_on_idxfunc(recursion_direction, h);
};

let meta_transform_intexpr_on_idxfunc =
    (recursion_direction: recursion_direction, z: intexpr => intexpr)
    : (idxfunc => idxfunc) =>
  meta_transform_ctx_intexpr_on_idxfunc(recursion_direction, (_, _) => z);

let meta_collect_idxfunc_on_idxfunc =
    (f: idxfunc => list('a)): (idxfunc => list('a)) => {
  let z = (g: idxfunc => list('a), e: idxfunc): list('a) =>
    switch (e) {
    | FH(_)
    | FL(_)
    | FD(_)
    | FHH(_) => []
    | FCompose(l) => List.flatten(List.map(g, l))
    | Pre(x) => g(x)
    | PreWrap(_) => []
    | FArg(_) => []
    | FUp(x) => g(x)
    | _ =>
      failwith(
        "meta_collect_idxfunc_on_idxfunc, not handled: "
        ++ string_of_idxfunc(e),
      )
    };

  recursion_collect(z, f);
};

let meta_collect_intexpr_on_idxfunc =
    (f: intexpr => list('a)): (idxfunc => list('a)) =>
  meta_collect_idxfunc_on_idxfunc(
    fun
    | [@implicit_arity] FH(a, b, c, d) => f(a) @ f(b) @ f(c) @ f(d)
    | [@implicit_arity] FL(n, m)
    | [@implicit_arity] FD(n, m) => f(n) @ f(m)
    | [@implicit_arity] FHH(a, b, c, d, l) =>
      f(a) @ f(b) @ f(c) @ f(d) @ List.flatten(List.map(f, l))
    | [@implicit_arity] FArg(_, l) => List.flatten(List.map(f, l))
    | _ => [],
  );

let meta_iter_idxfunc_on_idxfunc = (f: idxfunc => unit): (idxfunc => unit) =>
  (e: idxfunc) =>
    ignore(
      (
        meta_collect_idxfunc_on_idxfunc((e: idxfunc) => {
          f(e);
          [];
        })
      )(e),
    );

let meta_iter_intexpr_on_idxfunc = (f: intexpr => unit): (idxfunc => unit) =>
  (e: idxfunc) =>
    ignore(
      meta_collect_intexpr_on_idxfunc(
        (e: intexpr) => {
          f(e);
          [];
        },
        e,
      ),
    );

let rec func_range = (e: idxfunc): intexpr =>
  switch (e) {
  | [@implicit_arity] FH(_, range, _, _) => range
  | [@implicit_arity] FL(n, _) => n
  | [@implicit_arity] FD(n, _) => n
  | FCompose(l) => func_range(List.hd(l))
  | Pre(l) => func_range(l)
  | [@implicit_arity] FHH(_, r, _, _, _) => r
  /* | FUp(l) -> func_range l (\*FIXME really correct?*\) */
  | _ as e => failwith("func_range, not handled: " ++ string_of_idxfunc(e))
  };

let rec func_domain = (e: idxfunc): intexpr =>
  switch (e) {
  | [@implicit_arity] FH(domain, _, _, _) => domain
  | [@implicit_arity] FL(n, _) => n
  | [@implicit_arity] FD(n, _) => n
  | FCompose(l) => func_domain(List.hd(List.rev(l)))
  | Pre(l) => func_domain(l)
  | FUp(l) => func_domain(l) /*FIXME really correct?*/
  | [@implicit_arity] FHH(d, _, _, _, _) => d
  | [@implicit_arity] PreWrap(_, _, _, d) => d
  | [@implicit_arity] FArg(_, d) =>
    switch (last(d)) {
    | None => failwith("not a valid FArg")
    | Some(x) => x
    }
  | [@implicit_arity] FDown(f, _, _) => func_domain(f)
  | FNil => IConstant(0)
  };
/* | _ as e -> failwith("func_domain, not handled: "^(string_of_idxfunc e))		 */

let rec ctype_of_func = (e: idxfunc): ctype =>
  switch (e) {
  | FH(_) => Func([Int, Int])
  | FUp(f) =>
    switch (ctype_of_func(f)) {
    | Func(x) => Func([Int, ...x])
    | _ => failwith("ctype_of_func, not handled: " ++ string_of_idxfunc(e))
    }
  | FD(_) => Func([Int, Complex])
  | [@implicit_arity] FHH(_, _, _, _, n) =>
    let rec f = (l: int): list(ctype) =>
      if (l == 0) {
        [];
      } else {
        [Int, ...f(l - 1)];
      };
    Func(f(List.length(n) + 2));
  | FCompose([x, ..._]) => ctype_of_func(x) /*FIXME really correct?*/
  | [@implicit_arity] FArg(cvar, l) =>
    let rec derank = (ctype, count) =>
      if (count == 0) {
        ctype;
      } else {
        switch (ctype) {
        | Func([_, ...tl]) => derank(Func(tl), count - 1)
        | _ => failwith("not derankable")
        };
      };

    derank(ctype_of_cvar(cvar), List.length(l) - 1);
  | _ as e =>
    failwith("ctype_of_func, not handled: " ++ string_of_idxfunc(e))
  };

let rank_of_func = (e: idxfunc): int =>
  switch (ctype_of_func(e)) {
  | Func(l) => List.length(l) - 2
  | _ => failwith("rank_of_func, not handled: " ++ string_of_idxfunc(e))
  };

let meta_compose_idxfunc =
    (
      recursion_direction: recursion_direction,
      f: list(idxfunc) => list(idxfunc),
    )
    : (idxfunc => idxfunc) =>
  meta_transform_idxfunc_on_idxfunc(
    recursion_direction,
    fun
    | FCompose(l) => FCompose(f(l))
    | x => x,
  );

let rule_flatten_fcompose: idxfunc => idxfunc = (
  {
    let rec f = (l: list(idxfunc)): list(idxfunc) =>
      switch (l) {
      | [FCompose(a), ...tl] => f(a @ tl)
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_idxfunc(BottomUp, f);
  }:
    idxfunc => idxfunc
);

let rule_remove_unary_fcompose: idxfunc => idxfunc = (
  meta_transform_idxfunc_on_idxfunc(
    BottomUp,
    fun
    | FCompose([a]) => a
    | x => x,
  ):
    idxfunc => idxfunc
);

let rule_compose_FL_FH: idxfunc => idxfunc = (
  {
    let rec f = (l: list(idxfunc)): list(idxfunc) =>
      switch (l) {
      | [
          [@implicit_arity] FL(_ /*n1*/, k),
          [@implicit_arity] FH(m1, n2, IMul([m2, ...multl]), IConstant(1)),
          ...tl,
        ]
          when m1 == m2 =>
        f([[@implicit_arity] FH(m1, n2, IMul(multl), k), ...tl])
      | [
          FUp([@implicit_arity] FL(_, k)),
          [@implicit_arity] FHH(d, r, b, IConstant(1), [_, ...vstl]),
          ...tl,
        ] =>
        f([
          [@implicit_arity] FHH(d, r, b, k, [IConstant(1), ...vstl]),
          ...tl,
        ])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_idxfunc(BottomUp, f);
  }:
    idxfunc => idxfunc /*FIXME seems correct but needs guards for n and k!*/
  /*n1 = n2 is not checked because n could be mul(k,m) */
);

let rule_compose_FH_FH: idxfunc => idxfunc = (
  {
    let rec f = (l: list(idxfunc)): list(idxfunc) =>
      switch (l) {
      | [
          [@implicit_arity] FH(_, gnp, bp, sp),
          [@implicit_arity] FH(n, _, b, s),
          ...tl,
        ] =>
        f([
          [@implicit_arity]
          FH(n, gnp, IPlus([bp, IMul([sp, b])]), IMul([sp, s])),
          ...tl,
        ])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_idxfunc(BottomUp, f);
  }:
    idxfunc => idxfunc
  /*gn1 = gn2 is not checked because that could be non-obvious*/
);

let rule_compose_FHH_FHH: idxfunc => idxfunc = (
  {
    let rec f = (l: list(idxfunc)): list(idxfunc) =>
      switch (l) {
      | [
          [@implicit_arity] FHH(_, ra, ba, sa, vsa),
          [@implicit_arity] FHH(db, _, bb, sb, vsb),
          ...tl,
        ] =>
        let rec mul = (a: list(intexpr), b: list(intexpr)): list(intexpr) =>
          switch (a, b) {
          | ([], []) => []
          | ([], [y, ...ys]) => [IMul([sa, y]), ...mul([], ys)]
          | (x, []) => x
          | ([x, ...xs], [y, ...ys]) => [
              IPlus([x, IMul([sa, y])]),
              ...mul(xs, ys),
            ]
          };

        f([
          [@implicit_arity]
          FHH(
            db,
            ra,
            IPlus([ba, IMul([sa, bb])]),
            IMul([sa, sb]),
            mul(vsa, vsb),
          ),
          ...tl,
        ]);
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_idxfunc(BottomUp, f);
  }:
    idxfunc => idxfunc
  /*rb = da is not checked because that could be non-obvious*/
);

let rule_suck_inside_pre: idxfunc => idxfunc = (
  {
    let rec f = (l: list(idxfunc)): list(idxfunc) =>
      switch (l) {
      | [Pre(a), b, ...tl] => f([Pre(FCompose([a, b])), ...tl])
      | [a, ...tl] => [a, ...f(tl)]
      | [] => []
      };

    meta_compose_idxfunc(BottomUp, f);
  }:
    idxfunc => idxfunc
);

let rule_distribute_uprank: idxfunc => idxfunc = (
  meta_transform_idxfunc_on_idxfunc(
    TopDown,
    fun
    | FUp(FCompose(list)) => FCompose(List.map(x => FUp(x), list))
    | FUp(Pre(p)) => Pre(FUp(p))
    | x => x,
  ):
    idxfunc => idxfunc
);

let rule_distribute_downrank: idxfunc => idxfunc = (
  meta_transform_idxfunc_on_idxfunc(
    TopDown,
    fun
    | [@implicit_arity] FDown(FCompose(list), j, l) =>
      FCompose(List.map(x => [@implicit_arity] FDown(x, j, l), list))
    | [@implicit_arity] FDown(Pre(f), j, l) =>
      Pre([@implicit_arity] FDown(f, j, l))
    | [@implicit_arity] FDown([@implicit_arity] FArg(cvar, l), j, _) =>
      [@implicit_arity] FArg(cvar, [j, ...l])
    | [@implicit_arity] FDown(FUp(f), _, _) => f
    | [@implicit_arity] FDown(FNil, _, _) => FNil
    | x => x,
  ):
    idxfunc => idxfunc
);

let rule_uprank_FHH: idxfunc => idxfunc = (
  meta_transform_idxfunc_on_idxfunc(
    TopDown,
    fun
    | FUp([@implicit_arity] FHH(d, r, b, s, vs)) =>
      [@implicit_arity] FHH(d, r, b, s, [IConstant(0), ...vs])
    | x => x,
  ):
    idxfunc => idxfunc
);

let rule_downrank_FHH: idxfunc => idxfunc = (
  {
    let rec extract = (l: int, vs: list(intexpr)): (intexpr, list(intexpr)) =>
      switch (vs) {
      | [] => failwith("cannot downrank this FHH, it is of rank 0")
      | [x, ...xs] =>
        if (l == 0) {
          (x, xs);
        } else {
          let (a, b) = extract(l - 1, xs);
          (a, [x, ...b]);
        }
      };

    meta_transform_idxfunc_on_idxfunc(
      TopDown,
      fun
      | [@implicit_arity] FDown([@implicit_arity] FHH(d, r, b, s, vs), j, l) => {
          let (content, remainder) = extract(l, vs);
          [@implicit_arity]
          FHH(d, r, IPlus([b, IMul([content, j])]), s, remainder);
        }
      | x => x,
    );
  }:
    idxfunc => idxfunc
);

let rule_FHH_to_FH: idxfunc => idxfunc = (
  meta_transform_idxfunc_on_idxfunc(
    TopDown,
    fun
    | [@implicit_arity] FHH(d, r, b, s, []) =>
      [@implicit_arity] FH(d, r, b, s)
    | x => x,
  ):
    idxfunc => idxfunc
);

let idxfunc_rulemap =
  List.fold_left(
    (map, (name, rule)) => StringMap.add(name, rule, map),
    StringMap.empty,
    [
      ("Flatten FCompose", rule_flatten_fcompose),
      ("Remove unary fcompose", rule_remove_unary_fcompose),
      ("Rule suck inside pre", rule_suck_inside_pre),
      ("FCompose FHH with FHH", rule_compose_FHH_FHH),
      ("Compose_l_h", rule_compose_FL_FH),
      ("Compose_h_h", rule_compose_FH_FH),
      ("Distribute uprank", rule_distribute_uprank),
      ("Distribute downrank", rule_distribute_downrank),
      ("Downrank FHH", rule_downrank_FHH),
      ("Uprank FHH", rule_uprank_FHH),
      ("rule_FHH_to_FH", rule_FHH_to_FH),
    ]
    @ List.map(
        ((name, rule)) =>
          (
            "Lifted " ++ name,
            meta_transform_intexpr_on_idxfunc(BottomUp, rule),
          ),
        StringMap.bindings(intexpr_rulemap),
      ),
  );

let simplify_idxfunc = (f: idxfunc): idxfunc =>
  apply_rewriting_rules(idxfunc_rulemap, f);
