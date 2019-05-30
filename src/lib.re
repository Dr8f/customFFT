/******    TYPES    *******/
open Util;

open Spl;

open Intexpr;

open Idxfunc;

open Boolexpr;

module SplMap =
  Map.Make({
    type t = spl;
    let compare = Pervasives.compare;
  });

module IdxFuncMap =
  Map.Make({
    type t = idxfunc;
    let compare = Pervasives.compare;
  });

module IntExprSet =
  Set.Make({
    type t = intexpr;
    let compare = Pervasives.compare;
  });

type breakdown = (boolexpr, list((intexpr, intexpr)), spl, spl);

type rstep_unpartitioned = (string, spl, IntExprSet.t, list(breakdown));

type envfunc = (string, idxfunc, list(intexpr), list(idxfunc));

type closure = (list(envfunc), list(rstep_unpartitioned));

type breakdown_enhanced = (
  boolexpr,
  list((intexpr, intexpr)),
  spl,
  spl,
  option(spl),
  list(spl),
  spl,
);

type rstep_partitioned = (
  string,
  spl,
  IntExprSet.t,
  IntExprSet.t,
  IntExprSet.t,
  list(idxfunc),
  list(breakdown_enhanced),
);

type lib = (list(envfunc), list(rstep_partitioned));

type specified_arg = (string, int);

module SpecArgMap =
  Map.Make({
    type t = specified_arg;
    let compare = Pervasives.compare;
  });

module SpecArgSet =
  Set.Make({
    type t = specified_arg;
    let compare = Pervasives.compare;
  });

/******** PRINTING *******/

let string_of_breakdown_enhanced =
    (
      (
        condition,
        freedoms,
        desc,
        desc_with_calls,
        desc_with_calls_cons,
        desc_with_calls_to_construct,
        desc_with_calls_comp,
      ): breakdown_enhanced,
    )
    : string =>
  "---breakdown\n"
  ++ "   APPLICABILITY\t\t"
  ++ string_of_boolexpr(condition)
  ++ "\n"
  ++ "   FREEDOM\t\t\t"
  ++ String.concat(", ", List.map(string_of_intexpr_intexpr, freedoms))
  ++ "\n"
  ++ "   DESCEND\t\t\t"
  ++ string_of_spl(desc)
  ++ "\n"
  ++ "   DESCEND - CALLS\t\t"
  ++ string_of_spl(desc_with_calls)
  ++ "\n"
  ++ "   DESCEND - CALLS CONS\t\t"
  ++ (
    switch (desc_with_calls_cons) {
    | None => ""
    | Some(x) => string_of_spl(x)
    }
  )
  ++ "\n"
  ++ "   DESCEND - CALLS OBJ\t\t"
  ++ String.concat(
       "\n\t\t\t\t",
       List.map(string_of_spl, desc_with_calls_to_construct),
     )
  ++ "\n"
  ++ "   DESCEND - CALLS COMP\t\t"
  ++ string_of_spl(desc_with_calls_comp)
  ++ "\n";

let string_of_rstep_partitioned =
    ((name, rstep, cold, reinit, hot, funcs, breakdowns): rstep_partitioned)
    : string =>
  "NAME\t\t\t"
  ++ name
  ++ "\n"
  ++ "RS\t\t\t"
  ++ string_of_spl(rstep)
  ++ "\n"
  ++ "COLD\t\t\t"
  ++ String.concat(
       ", ",
       List.map(string_of_intexpr, IntExprSet.elements(cold)),
     )
  ++ "\n"
  ++ "REINIT\t\t\t"
  ++ String.concat(
       ", ",
       List.map(string_of_intexpr, IntExprSet.elements(reinit)),
     )
  ++ "\n"
  ++ "HOT\t\t\t"
  ++ String.concat(
       ", ",
       List.map(string_of_intexpr, IntExprSet.elements(hot)),
     )
  ++ "\n"
  ++ "FUNCS\t\t\t"
  ++ String.concat(", ", List.map(string_of_idxfunc, funcs))
  ++ "\n"
  ++ String.concat("", List.map(string_of_breakdown_enhanced, breakdowns))
  ++ "\n"
  ++ "\n";

let string_of_envfunc = ((name, idxfunc, args, fargs): envfunc): string =>
  "NAME\t\t\t"
  ++ name
  ++ "\n"
  ++ "FUNC\t\t\t"
  ++ string_of_idxfunc(idxfunc)
  ++ "\n"
  ++ "ARGS\t\t\t"
  ++ String.concat(", ", List.map(string_of_intexpr, args))
  ++ "\n"
  ++ "FARGS\t\t\t"
  ++ String.concat(", ", List.map(string_of_idxfunc, fargs))
  ++ "\n"
  ++ "\n";

let string_of_lib = ((funcs, rsteps): lib): string =>
  String.concat("", List.map(string_of_envfunc, funcs))
  ++ String.concat("", List.map(string_of_rstep_partitioned, rsteps));

/**********************
       CLOSURE
 ***********************/

let mark_RS: spl => spl = (
  meta_transform_spl_on_spl(
    BottomUp,
    fun
    | DFT(n) => RS(DFT(n))
    | x => x,
  ):
    spl => spl
);

let collect_RS: spl => list(spl) = (
  meta_collect_spl_on_spl(
    fun
    | RS(x) => [x]
    | _ => [],
  ):
    spl => list(spl)
);

let rec extract_constraints_func = (e: idxfunc): list((intexpr, intexpr)) => {
  let rec extract_constraints_within_fcompose =
          (e: list(idxfunc), res: list((intexpr, intexpr)))
          : list((intexpr, intexpr)) =>
    switch (e) {
    | [x, ...[y, ..._] as tl] =>
      extract_constraints_within_fcompose(
        tl,
        [(func_domain(x), func_range(y)), ...res],
      )
    | [_] => res
    | [] => res
    };

  switch (e) {
  | FCompose(l) =>
    extract_constraints_within_fcompose(
      l,
      List.flatten(List.map(extract_constraints_func, l)),
    )
  | Pre(x) => extract_constraints_func(x)
  | _ => []
  };
};

let extract_constraints_spl = (e: spl): list((intexpr, intexpr)) => {
  let rec inner_extract_constraints_spl = (e: spl): list((intexpr, intexpr)) => {
    let rec extract_constraints_within_compose =
            (e: list(spl), res: list((intexpr, intexpr)))
            : list((intexpr, intexpr)) =>
      switch (e) {
      | [x, ...[y, ..._] as tl] =>
        extract_constraints_within_compose(
          tl,
          [(spl_domain(x), spl_range(y)), ...res],
        )
      | [_] => res
      | [] => res
      };

    switch (e) {
    | Compose(l) =>
      extract_constraints_within_compose(
        l,
        List.flatten(List.map(inner_extract_constraints_spl, l)),
      )
    | Diag(x) => extract_constraints_func(x)
    | BB(x) => inner_extract_constraints_spl(x)
    | [@implicit_arity] GT(a, g, s, _) => [
        (spl_domain(a), func_domain(g)),
        (spl_range(a), func_domain(s)),
        ...inner_extract_constraints_spl(a),
      ]
    | _ => []
    };
  };

  List.map(
    ((x, y)) => (simplify_intexpr(x), simplify_intexpr(y)),
    inner_extract_constraints_spl(e),
  );
};

let rec reconcile_constraints_on_spl =
        ((constraints, spl): (list((intexpr, intexpr)), spl)): spl =>
  switch (constraints) {
  | [(l, r), ...tl] =>
    /* print_string ("processing constraint:"^(string_of_intexpr l)^"="^(string_of_intexpr r)^"\n"); */
    let f = (e: intexpr): intexpr =>
      if (e == r) {
        l;
      } else {
        e;
      };
    let t = (meta_transform_intexpr_on_spl(TopDown, f))(spl);
    reconcile_constraints_on_spl((
      List.map(((l, r)) => (f(l), f(r)), tl),
      t,
    ));
  | [] => spl
  };

let rec reconcile_constraints_on_idxfunc =
        ((constraints, idxfunc): (list((intexpr, intexpr)), idxfunc))
        : idxfunc =>
  switch (constraints) {
  | [(l, r), ...tl] =>
    let f = (e: intexpr): intexpr =>
      if (e == r) {
        l;
      } else {
        e;
      };
    reconcile_constraints_on_idxfunc((
      List.map(((l, r)) => (f(l), f(r)), tl),
      (meta_transform_intexpr_on_idxfunc(TopDown, f))(idxfunc),
    ));
  | [] => idxfunc
  };

let wrap_intexprs = (count: ref(int), i: intexpr): intexpr =>
  switch (i) {
  | IMul(_)
  | IPlus(_)
  | IDivPerfect(_)
  | IFreedom(_)
  | ILoopCounter(_)
  | IArg(_) =>
    count := count^ + 1;
    [@implicit_arity] ICountWrap(count^, i);
  | x => x
  };

let wrap_intexprs_on_spl = (e: spl): spl => {
  let count = ref(0);
  (meta_transform_intexpr_on_spl(TopDown, wrap_intexprs(count)))(e);
};

let wrap_intexprs_on_idxfunc = (e: idxfunc): idxfunc => {
  let count = ref(0);
  (meta_transform_intexpr_on_idxfunc(TopDown, wrap_intexprs(count)))(e);
};

let unwrap_idxfunc = (e: idxfunc): idxfunc => {
  let count = ref(0);
  let h = (e: idxfunc): idxfunc =>
    switch (e) {
    | [@implicit_arity] PreWrap((_, ct), _, _, d) =>
      print_string("now unwrapping " ++ string_of_idxfunc(e) ++ "\n");
      count := count^ + 1;
      Pre(
        [@implicit_arity]
        FArg(("lambda" ++ string_of_int(count^), ct), [d]),
      );
    | x => x
    };

  (meta_transform_idxfunc_on_idxfunc(TopDown, h))(e);
};

let unwrap_intexpr = (e: intexpr): intexpr =>
  switch (e) {
  | [@implicit_arity] ICountWrap(l, _) => IArg(l)
  | x => x
  };

let unwrap_spl = (e: spl): spl =>
  (meta_transform_idxfunc_on_spl(TopDown, unwrap_idxfunc))(
    (meta_transform_intexpr_on_spl(TopDown, unwrap_intexpr))(e),
  );

let rec mapify =
        (binds: list(intexpr), map: IntMap.t(intexpr)): IntMap.t(intexpr) =>
  switch (binds) {
  | [] => map
  | [[@implicit_arity] ICountWrap(p, expr), ...tl] =>
    mapify(tl, IntMap.add(p, expr, map))
  | _ => failwith("type is not supported")
  };

let collect_intexpr_binds = (i: intexpr): list(intexpr) =>
  switch (i) {
  | ICountWrap(_) => [i]
  | _ => []
  };

let replace_by_a_call_idxfunc =
    (f: idxfunc, idxfuncmap: ref(IdxFuncMap.t(envfunc))): idxfunc => {
  let ensure_name =
      (ffunc: idxfunc, args: list(intexpr), fargs: list(idxfunc)): string => {
    if (!IdxFuncMap.mem(ffunc, idxfuncmap^)) {
      let name =
        "Func_" ++ string_of_int(IdxFuncMap.cardinal(idxfuncmap^) + 1);
      idxfuncmap :=
        IdxFuncMap.add(ffunc, (name, ffunc, args, fargs), idxfuncmap^);
    };
    let (name, _, _, _) = IdxFuncMap.find(ffunc, idxfuncmap^);
    name;
  };

  let collect_farg = (i: idxfunc): list(idxfunc) =>
    switch (i) {
    | FArg(_) => [i]
    | _ => []
    };

  let wrap_naive = wrap_intexprs_on_idxfunc(f);
  let func_constraints = extract_constraints_func(wrap_naive);
  let wrapped =
    reconcile_constraints_on_idxfunc((func_constraints, wrap_naive));
  let domain = func_domain(f);
  let newdef =
    (meta_transform_intexpr_on_idxfunc(TopDown, unwrap_intexpr))(wrapped);
  let map =
    mapify(
      (meta_collect_intexpr_on_idxfunc(collect_intexpr_binds))(wrapped),
      IntMap.empty,
    );
  let new_args =
    List.map(
      fun
      | x => IArg(x),
      List.map(fst, IntMap.bindings(map)),
    );
  let args = List.map(snd, IntMap.bindings(map));
  let fargs = (meta_collect_idxfunc_on_idxfunc(collect_farg))(f);
  let name = ensure_name(newdef, new_args, fargs);
  let res =
    [@implicit_arity]
    PreWrap((name, ctype_of_func(f)), args, fargs, domain);
  let printer = (args: IntMap.t(intexpr)): string =>
    String.concat(
      ", ",
      List.map(
        ((i, e): (int, intexpr)) =>
          "( " ++ string_of_int(i) ++ " = " ++ string_of_intexpr(e) ++ ")",
        IntMap.bindings(args),
      ),
    );

  print_string(
    "function:\t\t"
    ++ string_of_idxfunc(f)
    ++ "\nwrap_naive:\t\t"
    ++ string_of_idxfunc(wrap_naive)
    ++ "\nconstraints:\t\t"
    ++ String.concat(
         ", ",
         List.map(
           ((g, d): (intexpr, intexpr)) =>
             "( "
             ++ string_of_intexpr(g)
             ++ " = "
             ++ string_of_intexpr(d)
             ++ ")",
           func_constraints,
         ),
       )
    ++ "\nwrapped:\t\t"
    ++ string_of_idxfunc(wrapped)
    ++ "\nname:\t\t\t"
    ++ name
    ++ "\nmap:\t\t\t"
    ++ printer(map)
    ++ "\nargs:\t\t\t"
    ++ String.concat(", ", List.map(string_of_intexpr, args))
    ++ "\nnew args:\t\t"
    ++ String.concat(", ", List.map(string_of_intexpr, new_args))
    ++ "\nfargs:\t\t\t"
    ++ String.concat(", ", List.map(string_of_idxfunc, fargs))
    ++ "\nnewdef:\t\t\t"
    ++ string_of_idxfunc(newdef)
    ++ "\nres:\t\t\t"
    ++ string_of_idxfunc(res)
    ++ "\n\n\n",
  );
  res;
};

let reintegrate_RS = (e: spl, canonized: list(spl)): spl => {
  let rem = ref(canonized);
  let f = (e: spl): spl =>
    switch (e) {
    | RS(_) =>
      let hd = List.hd(rem^);
      rem := List.tl(rem^);
      RS(hd);
    | x => x
    };

  (meta_transform_spl_on_spl(TopDown, f))(e);
};

let drop_RS: spl => spl = (
  {
    let g = (e: spl): spl =>
      switch (e) {
      | RS(x) => x
      | x => x
      };

    meta_transform_spl_on_spl(BottomUp, g);
  }:
    spl => spl
);

let replace_by_a_call_spl =
    ((wrapped, (name, unwrapped)): (spl, (string, spl))): spl => {
  let collect_idxfunc_binds = (i: idxfunc): list(idxfunc) =>
    switch (i) {
    | PreWrap(_) => [i]
    | _ => []
    };

  let res =
    [@implicit_arity]
    UnpartitionnedCall(
      name,
      mapify(
        meta_collect_intexpr_on_spl(collect_intexpr_binds, wrapped),
        IntMap.empty,
      ),
      meta_collect_idxfunc_on_spl(collect_idxfunc_binds, wrapped),
      spl_range(unwrapped),
      spl_domain(unwrapped),
    );
  /* print_string ("WIP REPLACING:\nwrapped:"^(string_of_spl wrapped)^"\nunwrapped:"^(string_of_spl unwrapped)^"\nres:"^(string_of_spl res)^"\n\n"); */
  res;
};

let collect_args = (rstep: spl): IntExprSet.t => {
  let args = ref(IntExprSet.empty);
  let g = (e: intexpr): _ =>
    switch (e) {
    | IArg(_) => args := IntExprSet.add(e, args^)
    | _ => ()
    };

  meta_iter_intexpr_on_spl(g, rstep);
  args^;
};

let localize_precomputations = (e: Spl.spl): Spl.spl => {
  let g = (ctx, a) =>
    switch (a) {
    | Spl.Diag(Idxfunc.Pre(f)) =>
      let gt_list = List.flatten(List.map(Spl.collect_GT, ctx));
      if (List.length(gt_list) == 1) {
        switch (List.hd(gt_list)) {
        | [@implicit_arity] Spl.GT(_, _, _, l) =>
          if (List.length(l) == 1) {
            [@implicit_arity]
            Spl.DiagData(
              f,
              [@implicit_arity]
              Idxfunc.FHH(
                Idxfunc.func_domain(f),
                Idxfunc.func_domain(f),
                Intexpr.IConstant(0),
                Intexpr.IConstant(1),
                [Idxfunc.func_domain(f)],
              ),
            );
          } else if (List.length(l) == 2) {
            [@implicit_arity]
            Spl.DiagData(
              f,
              [@implicit_arity]
              Idxfunc.FHH(
                Idxfunc.func_domain(f),
                Idxfunc.func_domain(f),
                Intexpr.IConstant(0),
                Intexpr.IConstant(1),
                [Idxfunc.func_domain(f), Idxfunc.func_domain(f)],
              ),
            );
          } else {
            /*FIXME not quite sure this is correct*/

            failwith(
              "not implemented yet, there certainly ought to be a match between the GT rank and the FHH below",
            );
          }
        | _ => assert(false)
        };
      } else if (List.length(gt_list) == 0) {
        [@implicit_arity]
        Spl.DiagData(
          f,
          [@implicit_arity]
          Idxfunc.FH(
            Idxfunc.func_domain(f),
            Idxfunc.func_domain(f),
            Intexpr.IConstant(0),
            Intexpr.IConstant(1),
          ),
        );
      } else {
        failwith("what to do?");
      };
    | x => x
    };

  Spl.simplify_spl(Spl.meta_transform_ctx_spl_on_spl(BottomUp, g, e));
};

let create_breakdown =
    (
      rstep: spl,
      idxfuncmap: ref(IdxFuncMap.t(envfunc)),
      algo: spl => (boolexpr, list((intexpr, intexpr)), spl),
      ensure_name: spl => string,
    )
    : (boolexpr, list((intexpr, intexpr)), spl, spl) => {
  let (condition, freedoms, naive_desc) = algo(rstep);

  let desc = simplify_spl(mark_RS(naive_desc));
  print_string("Desc:\t\t" ++ string_of_spl(desc) ++ "\n");

  let simplification_constraints = extract_constraints_spl(desc);
  print_string("Simplifying constraints\t\n");

  let simplified =
    reconcile_constraints_on_spl((simplification_constraints, desc));
  print_string("Simplified desc:\t\t" ++ string_of_spl(simplified) ++ "\n");

  let rses = collect_RS(simplified);
  print_string(
    "***rses***:\n"
    ++ String.concat(",\n", List.map(string_of_spl, rses))
    ++ "\n\n",
  );

  let wrap_precomputations = (e: spl): spl => {
    let transf = (i: idxfunc): idxfunc =>
      switch (i) {
      | Pre(f) => replace_by_a_call_idxfunc(f, idxfuncmap)
      | x => x
      };

    (meta_transform_idxfunc_on_spl(TopDown, transf))(e);
  };

  let wrapped_precomps = List.map(wrap_precomputations, rses);
  print_string(
    "WIP DESC wrapped precomps:\n"
    ++ String.concat(",\n", List.map(string_of_spl, wrapped_precomps))
    ++ "\n\n",
  ); /* WIP */

  let wrapped_intexpr = List.map(wrap_intexprs_on_spl, wrapped_precomps);
  /* print_string ("WIP DESC wrapped intexprs:\n"^(String.concat ",\n" (List.map string_of_spl wrapped_intexpr))^"\n\n"); */

  let constraints = List.map(extract_constraints_spl, wrapped_intexpr);
  let wrapped_RSes =
    List.map(
      reconcile_constraints_on_spl,
      List.combine(constraints, wrapped_intexpr),
    );

  /* print_string ("WIP DESC wrapped:\n"^(String.concat ",\n" (List.map string_of_spl wrapped_RSes))^"\n\n"); (\* WIP *\) */

  let new_steps = List.map(unwrap_spl, wrapped_RSes);
  /* print_string ("WIP DESC new steps:\n"^(String.concat ",\n" (List.map string_of_spl new_steps))^"\n\n"); (\* WIP *\) */

  let new_names = List.map(ensure_name, new_steps);
  /* print_string ("WIP DESC newnames:\n"^(String.concat ",\n" (new_names))^"\n\n"); (\* WIP *\) */

  let extracts_with_calls =
    List.map(
      replace_by_a_call_spl,
      List.combine(wrapped_RSes, List.combine(new_names, rses)),
    );
  /* print_string ("WIP DESC extracts_with_calls:\n"^(String.concat ",\n" (List.map string_of_spl extracts_with_calls))^"\n\n"); (\* WIP *\) */

  let desc_with_calls =
    drop_RS(reintegrate_RS(simplified, extracts_with_calls));
  /* print_string ("WIP DESC with_calls:\n"^(string_of_spl desc_with_calls)^"\n\n"); (\* WIP *\) */

  (
    condition,
    freedoms,
    simplified,
    localize_precomputations(desc_with_calls),
  );
};

let compute_the_closure =
    (
      stems: list(spl),
      algos: list(spl => (boolexpr, list((intexpr, intexpr)), spl)),
    )
    : closure => {
  let rsteps = ref([]);
  let idxfuncmap = ref(IdxFuncMap.empty);

  let under_consideration = ref([]);
  let namemap = ref(SplMap.empty);
  let count = ref(0);
  let register_name = (rstep: spl): _ => {
    count := count^ + 1;
    let name = "RS" ++ string_of_int(count^);
    namemap := SplMap.add(rstep, name, namemap^);
    under_consideration := under_consideration^ @ [rstep];
  };

  let ensure_name = (rstep: spl): string => {
    if (!SplMap.mem(rstep, namemap^)) {
      register_name(rstep);
    };
    SplMap.find(rstep, namemap^);
  };

  List.iter(register_name, stems);
  while (List.length(under_consideration^) !== 0) {
    /* print_string "LOOP\n"; */
    let rstep = List.hd(under_consideration^);
    under_consideration := List.tl(under_consideration^);
    /* print_string ("WIP RSTEP:\t\t"^(string_of_spl rstep)^"\n"); (\* WIP *\) */
    let name = ensure_name(rstep);
    let args = collect_args(rstep);

    let breakdowns = ref([]);
    let f = algo =>
      try (
        breakdowns :=
          [
            create_breakdown(rstep, idxfuncmap, algo, ensure_name),
            ...breakdowns^,
          ]
      ) {
      | Algo.AlgoNotApplicable(s) =>
        print_string("Cannot apply algo: " ++ s ++ "\n")
      };
    List.iter(f, algos);
    rsteps := rsteps^ @ [(name, rstep, args, breakdowns^)];
  };

  (List.map(snd, IdxFuncMap.bindings(idxfuncmap^)), rsteps^);
};

let dependency_map_of_rsteps =
    (rsteps: list(rstep_unpartitioned)): SpecArgMap.t(SpecArgSet.t) => {
  let depmap = ref(SpecArgMap.empty);
  let per_rstep = ((name, _, _, breakdowns): rstep_unpartitioned): _ => {
    let per_rule = ((_, _, _, desc_with_calls): breakdown): _ =>
      meta_iter_spl_on_spl(
        fun
        | [@implicit_arity] UnpartitionnedCall(callee, vars, _, _, _) => {
            let g = (arg: int, expr: intexpr): _ => {
              let key = (callee, arg);
              let h = (e: intexpr): _ =>
                switch (e) {
                | IArg(i) =>
                  let new_content = (name, i);
                  depmap :=
                    (
                      if (SpecArgMap.mem(key, depmap^)) {
                        SpecArgMap.add(
                          key,
                          SpecArgSet.add(
                            new_content,
                            SpecArgMap.find(key, depmap^),
                          ),
                          depmap^,
                        );
                      } else {
                        SpecArgMap.add(
                          key,
                          SpecArgSet.singleton(new_content),
                          depmap^,
                        );
                      }
                    );
                | _ => ()
                };

              meta_iter_intexpr_on_intexpr(h, expr);
            };

            IntMap.iter(g, vars);
          }
        | _ => (),
        desc_with_calls,
      );

    List.iter(per_rule, breakdowns);
  };

  List.iter(per_rstep, rsteps);
  depmap^;
};

let initial_hots_of_rsteps =
    (rsteps: list(rstep_unpartitioned)): SpecArgSet.t => {
  let hot_set = ref(SpecArgSet.empty);
  let per_rstep = ((_, _, _, breakdowns): rstep_unpartitioned): _ => {
    let per_rule = ((_, _, _, desc_with_calls): breakdown): _ =>
      meta_iter_spl_on_spl(
        fun
        | [@implicit_arity] UnpartitionnedCall(callee, vars, _, _, _) => {
            let g = (arg: int, expr: intexpr): _ => {
              let h = (e: intexpr): _ =>
                switch (e) {
                | ILoopCounter(_) =>
                  hot_set := SpecArgSet.add((callee, arg), hot_set^)
                | _ => ()
                };

              meta_iter_intexpr_on_intexpr(h, expr);
            };

            IntMap.iter(g, vars);
          }
        | _ => (),
        desc_with_calls,
      );

    List.iter(per_rule, breakdowns);
  };

  List.iter(per_rstep, rsteps);
  hot_set^;
};

let initial_colds_of_rsteps =
    (rsteps: list(rstep_unpartitioned)): SpecArgSet.t => {
  let cold_set = ref(SpecArgSet.empty);

  let init_rstep = ((name, rstep, _, breakdowns): rstep_unpartitioned): _ => {
    let add_args_to_cold = (e: intexpr): _ =>
      switch (e) {
      | IArg(i) => cold_set := SpecArgSet.add((name, i), cold_set^)
      | _ => ()
      };

    /* all arguments in the pre() marker must be cold */
    let add_all_pre_to_cold = (ctx: list(spl), e: idxfunc): _ =>
      switch (e) {
      | Pre(x) =>
        /* all args in Pre should be cold*/
        meta_iter_intexpr_on_idxfunc(add_args_to_cold, x);
        /* and all the loop bounds of wrapping GTs */
        let f = (
          fun
          | [@implicit_arity] GT(_, _, _, l) =>
            List.iter(add_args_to_cold, l)
          | _ => ()
        );

        List.iter(meta_iter_spl_on_spl(f), ctx);
      | _ => ()
      };

    meta_iter_ctx_idxfunc_on_spl(add_all_pre_to_cold, rstep);

    let init_rule = ((condition, freedoms, _, _): breakdown): _ => {
      /* all arguments in condition (intexpr list) */
      /* print_string ("AND the magic condition is:"^(string_of_boolexpr condition)^"\n"); */
      meta_iter_intexpr_on_boolexpr(add_args_to_cold, condition);

      /* all arguments in freedoms ((intexpr*intexpr) list) must be cold */
      List.iter(
        meta_iter_intexpr_on_intexpr(add_args_to_cold),
        List.map(snd, freedoms),
      );
    };

    List.iter(init_rule, breakdowns);
  };

  List.iter(init_rstep, rsteps);
  cold_set^;
};

let backward_propagation =
    (init_set: SpecArgSet.t, dependency_map: SpecArgMap.t(SpecArgSet.t))
    : SpecArgSet.t => {
  let res = ref(init_set);
  let dirty = ref(true);
  let f = (callee: specified_arg, caller_set: SpecArgSet.t): _ =>
    if (SpecArgSet.mem(callee, res^)) {
      let g = (caller: specified_arg): _ =>
        if (!SpecArgSet.mem(caller, res^)) {
          res := SpecArgSet.add(caller, res^);
          dirty := true;
        };

      SpecArgSet.iter(g, caller_set);
    };

  while (dirty^) {
    dirty := false;
    SpecArgMap.iter(f, dependency_map);
  };
  res^;
};

let forward_propagation =
    (init_set: SpecArgSet.t, dependency_map: SpecArgMap.t(SpecArgSet.t))
    : SpecArgSet.t => {
  let res = ref(init_set);
  let dirty = ref(true);
  let forward_hot_propagation =
      (callee: specified_arg, caller_set: SpecArgSet.t): _ =>
    if (!SpecArgSet.mem(callee, res^)) {
      let g = (caller: specified_arg): _ =>
        if (SpecArgSet.mem(caller, res^)) {
          res := SpecArgSet.add(callee, res^);
          dirty := true;
        };

      SpecArgSet.iter(g, caller_set);
    };

  while (dirty^) {
    dirty := false;
    SpecArgMap.iter(forward_hot_propagation, dependency_map);
  };
  res^;
};

let filter_by_rstep = (name: string, s: SpecArgSet.t): IntExprSet.t => {
  let res = ref(IntExprSet.empty);
  let f = ((rs, i): specified_arg): _ =>
    if (rs == name) {
      res := IntExprSet.add(IArg(i), res^);
    };

  SpecArgSet.iter(f, s);
  res^;
};

let partition_map_of_rsteps =
    (rsteps: list(rstep_unpartitioned))
    : (
        StringMap.t(IntExprSet.t),
        StringMap.t(IntExprSet.t),
        StringMap.t(IntExprSet.t),
      ) => {
  let dependency_map = dependency_map_of_rsteps(rsteps);
  let initial_colds = initial_colds_of_rsteps(rsteps);
  let initial_hots = initial_hots_of_rsteps(rsteps);
  let all_colds = backward_propagation(initial_colds, dependency_map);
  let all_hots = forward_propagation(initial_hots, dependency_map);

  let colds = ref(StringMap.empty);
  let reinits = ref(StringMap.empty);
  let hots = ref(StringMap.empty);
  let partition_args = ((name, _, args, _): rstep_unpartitioned): _ => {
    let necessarily_colds = filter_by_rstep(name, all_colds);
    let necessarily_hots = filter_by_rstep(name, all_hots);
    let not_constrained =
      IntExprSet.diff(
        args,
        IntExprSet.union(necessarily_colds, necessarily_hots),
      );
    let reinit = IntExprSet.inter(necessarily_colds, necessarily_hots);
    reinits := StringMap.add(name, reinit, reinits^);
    colds :=
      StringMap.add(name, IntExprSet.diff(necessarily_colds, reinit), colds^);
    hots :=
      StringMap.add(
        name,
        IntExprSet.diff(
          IntExprSet.union(necessarily_hots, not_constrained),
          reinit,
        ),
        hots^,
      );
  }; /* as hot as possible */

  List.iter(partition_args, rsteps);
  (colds^, reinits^, hots^);
};

/* FIXME second arg is never used in this function ?! how does this even works? */
let depends_on = (funcs: list(idxfunc), _: intexpr): bool => {
  /* print_string ("Does ["^(String.concat "; " (List.map string_of_idxfunc funcs))^"] depends on "^(string_of_intexpr var)^"?\n"); */
  let res = ref(false);
  let f = (idxfunc: idxfunc): _ =>
    switch (idxfunc) {
    | PreWrap(_) => res := true
    | _ => failwith("This function is not a prewrap ?!")
    };

  List.iter(x => meta_iter_idxfunc_on_idxfunc(f, x), funcs);
  /* print_string ((string_of_bool !res)^"\n\n"); */
  res^;
};

let lib_from_closure = ((funcs, rsteps): closure): lib => {
  let filter_by =
      (args: IntMap.t(intexpr), set: IntExprSet.t): list(intexpr) =>
    List.map(
      snd,
      List.filter(
        ((i, _): (int, intexpr)) => IntExprSet.mem(IArg(i), set),
        IntMap.bindings(args),
      ),
    );

  let (cold, reinit, hot) = partition_map_of_rsteps(rsteps);
  let f =
      ((name, rstep, _, breakdowns): rstep_unpartitioned): rstep_partitioned => {
    let g =
        ((condition, freedoms, desc, desc_with_calls): breakdown)
        : breakdown_enhanced => {
      let childcount = ref(0);
      let h = (e: spl): spl =>
        switch (e) {
        | [@implicit_arity]
          UnpartitionnedCall(callee, args, funcs, range, domain) =>
          childcount := childcount^ + 1;
          [@implicit_arity]
          PartitionnedCall(
            childcount^,
            callee,
            filter_by(args, StringMap.find(callee, cold)),
            filter_by(args, StringMap.find(callee, reinit)),
            filter_by(args, StringMap.find(callee, hot)),
            funcs,
            range,
            domain,
          );
        | x => x
        };

      let partitioned =
        (meta_transform_spl_on_spl(BottomUp, h))(desc_with_calls);

      let j = (e: spl): spl =>
        switch (e) {
        | [@implicit_arity]
          ISum(
            _,
            _,
            [@implicit_arity]
            PartitionnedCall(childcount, callee, cold, [], _, [], _, _),
          ) =>
          [@implicit_arity] Construct(childcount, callee, cold, [])
        | [@implicit_arity]
          ISum(
            i,
            high,
            [@implicit_arity]
            PartitionnedCall(
              childcount,
              callee,
              cold,
              reinit,
              _,
              funcs,
              _,
              _,
            ),
          ) =>
          [@implicit_arity]
          ISumReinitConstruct(
            childcount,
            i,
            high,
            callee,
            cold,
            reinit,
            funcs,
          )
        | [@implicit_arity]
          PartitionnedCall(childcount, callee, cold, _, _, funcs, _, _) =>
          [@implicit_arity] Construct(childcount, callee, cold, funcs)
        | x => x
        };

      let k = (e: spl): spl =>
        switch (e) {
        | [@implicit_arity]
          ISum(
            i,
            high,
            [@implicit_arity]
            PartitionnedCall(
              childcount,
              callee,
              _,
              _,
              hot,
              funcs,
              range,
              domain,
            ),
          )
            when depends_on(funcs, i) =>
          [@implicit_arity]
          ISumReinitCompute(childcount, i, high, callee, hot, range, domain) /*this should only fire if needed, there are funcs that are dependent on i*/
        | [@implicit_arity]
          PartitionnedCall(childcount, callee, _, _, hot, _, range, domain) =>
          [@implicit_arity] Compute(childcount, callee, hot, range, domain) /*this is the default, most general case*/ /*the combination of the two impose a TopDown approach*/
        | x => x
        };

      let realize_precomputations = (s: spl): spl => {
        let e =
          meta_transform_spl_on_spl(
            BottomUp,
            fun
            | [@implicit_arity] DiagData(f, loc) =>
              [@implicit_arity] SideArg(Diag(f), loc)
            | x => x,
            s,
          );
        simplify_spl(e);
      };

      let construct =
        realize_precomputations(
          (meta_transform_spl_on_spl(TopDown, j))(partitioned),
        );
      let collect_constructs: spl => list(spl) = (
        meta_collect_spl_on_spl(
          fun
          | Construct(_) as x => [x]
          | ISumReinitConstruct(_) as x => [x]
          | _ => [],
        ):
          spl => list(spl)
      );

      let prepare_precomputations = (a: spl): option(spl) =>
        switch (a) {
        | [@implicit_arity] Spl.SideArg(x, _) => Some(x)
        | _ => None
        };

      (
        condition,
        freedoms,
        desc,
        partitioned,
        prepare_precomputations(construct),
        collect_constructs(construct),
        (meta_transform_spl_on_spl(TopDown, k))(partitioned),
      );
    };

    let lambda_args = {
      let rec collect_lambdas = (i: idxfunc): list(idxfunc) =>
        switch (i) {
        | FArg(_) => [i]
        | Pre(f) => collect_lambdas(f)
        | _ => []
        };

      (meta_collect_idxfunc_on_spl(collect_lambdas))(rstep);
    };

    (
      name,
      rstep,
      StringMap.find(name, cold),
      StringMap.find(name, reinit),
      StringMap.find(name, hot),
      lambda_args,
      List.map(g, breakdowns),
    );
  };

  (funcs, List.map(f, rsteps));
};

let make_lib =
    (
      functionalities: list(spl),
      algos: list(spl => (boolexpr, list((intexpr, intexpr)), spl)),
    )
    : lib => {
  let closure = compute_the_closure(functionalities, algos);
  lib_from_closure(closure);
};
