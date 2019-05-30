open Util;

open Lib;

open Code;

let _rs = Ctype.Env("RS");

let _at = "at";

let _compute = "compute";

let _rule = [@implicit_arity] Var(Ctype.Int, "_rule");

let _dat = [@implicit_arity] Var(Ctype.Ptr(Ctype.Complex), "_dat");

let _internal_error =
  [@implicit_arity] Var(Ctype.Ptr(Ctype.Complex), "_internal_error");

let build_child_var = (num: int): expr =>
  [@implicit_arity] Var(Ctype.Ptr(_rs), "child" ++ string_of_int(num));

let expr_of_intexpr = (intexpr: Intexpr.intexpr): expr =>
  switch (intexpr) {
  | Intexpr.IConstant(x) => IConst(x)
  | _ => [@implicit_arity] Var(Ctype.Int, Intexpr.string_of_intexpr(intexpr))
  };

let _output = [@implicit_arity] Var(Ctype.Ptr(Ctype.Complex), "Y");

let _input = [@implicit_arity] Var(Ctype.Ptr(Ctype.Complex), "X");

let rec expr_of_idxfunc = (idxfunc: Idxfunc.idxfunc): expr =>
  switch (idxfunc) {
  | [@implicit_arity] Idxfunc.FArg(cvar, _) =>
    [@implicit_arity]
    Var(Ctype.Ptr(Ctype.ctype_of_cvar(cvar)), Ctype.name_of_cvar(cvar))
  | [@implicit_arity] Idxfunc.PreWrap(cvar, l, funcs, _) =>
    [@implicit_arity]
    FunctionCall(
      Ctype.name_of_cvar(cvar),
      List.map(expr_of_intexpr, l) @ List.map(expr_of_idxfunc, funcs),
    )
  | _ =>
    failwith(
      "expr_of_idxfunc, not handled: " ++ Idxfunc.string_of_idxfunc(idxfunc),
    )
  };

let rec code_of_func =
        (func: Idxfunc.idxfunc, (input, code): (expr, list(code)))
        : (expr, list(code)) => {
  print_string(
    "Now building code for " ++ Idxfunc.string_of_idxfunc(func) ++ "\n",
  );
  switch (func) {
  | [@implicit_arity] Idxfunc.FH(_, _, b, s) =>
    let output = gen_var#get(Ctype.Int, "t");
    (
      output,
      code
      @ [
        Declare(output),
        [@implicit_arity]
        Assign(
          output,
          [@implicit_arity]
          Plus(
            expr_of_intexpr(b),
            [@implicit_arity] Mul(expr_of_intexpr(s), input),
          ),
        ),
      ],
    );
  | [@implicit_arity] Idxfunc.FD(n, k) =>
    let output = gen_var#get(Ctype.Complex, "c");
    (
      output,
      code
      @ [
        Declare(output),
        [@implicit_arity]
        Assign(
          output,
          [@implicit_arity]
          FunctionCall(
            "omega",
            [
              expr_of_intexpr(n),
              UniMinus(
                [@implicit_arity]
                Mul(
                  [@implicit_arity] Mod(input, expr_of_intexpr(k)),
                  [@implicit_arity] Divide(input, expr_of_intexpr(k)),
                ),
              ),
            ],
          ),
        ),
      ],
    );
  | [@implicit_arity] Idxfunc.FArg((_, Ctype.Func(ctypes)), mylist) =>
    switch (last(ctypes)) {
    | None => failwith("empty type list")
    | Some(x) =>
      let output = gen_var#get(x, "c");
      (
        output,
        code
        @ [
          Declare(output),
          [@implicit_arity]
          Assign(
            output,
            [@implicit_arity]
            MethodCall(
              expr_of_idxfunc(func),
              _at,
              List.map(expr_of_intexpr, drop_last(mylist)) @ [input],
            ),
          ),
        ],
      );
    }
  | Idxfunc.FCompose(l) => List.fold_right(code_of_func, l, (input, []))
  | _ =>
    failwith(
      "code_of_func, not handled: " ++ Idxfunc.string_of_idxfunc(func),
    )
  };
};

let rec code_of_spl = (output: expr, input: expr, e: Spl.spl): code =>
  switch (e) {
  | Spl.Compose(l) =>
    let ctype = Ctype.Complex;
    let buffernames = {
      let count = ref(0);
      let g = (res: list(expr), _: Spl.spl): list(expr) => {
        count := count^ + 1;
        [
          [@implicit_arity]
          Var(Ctype.Ptr(ctype), "T" ++ string_of_int(count^)),
          ...res,
        ];
      };

      List.fold_left(g, [], List.tl(l));
    };
    let out_in_spl =
      List.combine(
        List.combine(buffernames @ [output], [input, ...buffernames]),
        List.rev(l),
      );
    let buffers =
      List.combine(
        buffernames,
        List.map(Spl.spl_range, List.rev(List.tl(l))),
      );
    Chain(
      List.map(((output, _)) => Declare(output), buffers)
      @ List.map(
          ((output, size)) =>
            [@implicit_arity]
            ArrayAllocate(output, ctype, expr_of_intexpr(size)),
          buffers,
        )
      @ List.map(
          (((output, input), spl)) => code_of_spl(output, input, spl),
          out_in_spl,
        )
      @ List.map(
          ((output, size)) =>
            [@implicit_arity] ArrayDeallocate(output, expr_of_intexpr(size)),
          buffers,
        ),
    );
  | [@implicit_arity] Spl.ISum(i, count, content) =>
    [@implicit_arity]
    Loop(
      expr_of_intexpr(i),
      expr_of_intexpr(count),
      code_of_spl(output, input, content),
    )
  | [@implicit_arity] Spl.Compute(numchild, rs, hot, _, _) =>
    Ignore(
      [@implicit_arity]
      MethodCall(
        [@implicit_arity]
        Cast(build_child_var(numchild), Ctype.Ptr(Ctype.Env(rs))),
        _compute,
        [output, input, ...List.map(expr_of_intexpr, hot)],
      ),
    )
  | [@implicit_arity] Spl.ISumReinitCompute(numchild, i, count, rs, hot, _, _) =>
    [@implicit_arity]
    Loop(
      expr_of_intexpr(i),
      expr_of_intexpr(count),
      Ignore(
        [@implicit_arity]
        MethodCall(
          AddressOf(
            [@implicit_arity]
            Nth(
              [@implicit_arity]
              Cast(build_child_var(numchild), Ctype.Ptr(Ctype.Env(rs))),
              expr_of_intexpr(i),
            ),
          ),
          _compute,
          [output, input, ...List.map(expr_of_intexpr, hot)],
        ),
      ),
    )
  | Spl.F(2) =>
    Chain([
      [@implicit_arity]
      Assign(
        [@implicit_arity] Nth(output, IConst(0)),
        [@implicit_arity]
        Plus(
          [@implicit_arity] Nth(input, IConst(0)),
          [@implicit_arity] Nth(input, IConst(1)),
        ),
      ),
      [@implicit_arity]
      Assign(
        [@implicit_arity] Nth(output, IConst(1)),
        [@implicit_arity]
        Minus(
          [@implicit_arity] Nth(input, IConst(0)),
          [@implicit_arity] Nth(input, IConst(1)),
        ),
      ),
    ])
  | Spl.S(idxfunc) =>
    let var = gen_var#get(Ctype.Int, "t");
    let (index, codelines) = code_of_func(idxfunc, (var, []));
    [@implicit_arity]
    Loop(
      var,
      expr_of_intexpr(Spl.spl_domain(e)),
      Chain(
        codelines
        @ [
          [@implicit_arity]
          Assign(
            [@implicit_arity] Nth(output, index),
            [@implicit_arity] Nth(input, var),
          ),
        ],
      ),
    );
  | Spl.G(idxfunc) =>
    let var = gen_var#get(Ctype.Int, "t");
    let (index, codelines) = code_of_func(idxfunc, (var, []));
    [@implicit_arity]
    Loop(
      var,
      expr_of_intexpr(Spl.spl_range(e)),
      Chain(
        codelines
        @ [
          [@implicit_arity]
          Assign(
            [@implicit_arity] Nth(output, var),
            [@implicit_arity] Nth(input, index),
          ),
        ],
      ),
    );

  | Spl.Diag(idxfunc) =>
    /* actually computing the functions*/
    let var = gen_var#get(Ctype.Int, "t");
    let (precomp, codelines) = code_of_func(idxfunc, (var, []));
    Chain([
      [@implicit_arity]
      Loop(
        var,
        expr_of_intexpr(Spl.spl_range(e)),
        Chain(
          codelines
          @ [
            [@implicit_arity]
            Assign([@implicit_arity] Nth(output, var), precomp),
          ],
        ),
      ),
    ]);

  | [@implicit_arity] Spl.DiagData(_, g) =>
    /* just loading the the stored data*/
    let var = gen_var#get(Ctype.Int, "t");
    let (precomp, codelines) = code_of_func(g, (var, []));
    [@implicit_arity]
    Loop(
      var,
      expr_of_intexpr(Spl.spl_range(e)),
      Chain(
        codelines
        @ [
          [@implicit_arity]
          Assign(
            [@implicit_arity] Nth(output, var),
            [@implicit_arity]
            Mul(
              [@implicit_arity] Nth(input, var),
              [@implicit_arity]
              Nth(
                [@implicit_arity] Cast(_dat, Ctype.Ptr(Ctype.Complex)),
                precomp,
              ),
            ),
          ),
        ],
      ),
    );

  | [@implicit_arity] Spl.GT(a, g, s, [v]) =>
    let i = Intexpr.gen_loop_counter#get();
    let spl =
      [@implicit_arity]
      Spl.ISum(
        i,
        v,
        Spl.Compose([
          Spl.S([@implicit_arity] Idxfunc.FDown(s, i, 0)),
          [@implicit_arity] Spl.Down(a, i, 0),
          Spl.G([@implicit_arity] Idxfunc.FDown(g, i, 0)),
        ]),
      ); /*the Down here pushes the downrank to the SideArg*/
    code_of_spl(output, input, Spl.simplify_spl(spl));
  | Spl.BB(spl) => /* Compiler.compile_bloc */ code_of_spl(output, input, spl) /*FIXME re-enable compile*/
  | _ => failwith("code_of_spl, not handled: " ++ Spl.string_of_spl(e))
  };

let code_of_rstep = (rstep_partitioned: rstep_partitioned): code => {
  let collect_children =
      ((_, _, _, _, _, _, breakdowns): rstep_partitioned): list(expr) => {
    let res = ref(IntSet.empty);
    let g = ((_, _, _, _, _, constructs, _): breakdown_enhanced): _ =>
      List.iter(
        fun
        | [@implicit_arity] Spl.Construct(numchild, _, _, _)
        | [@implicit_arity]
          Spl.ISumReinitConstruct(numchild, _, _, _, _, _, _) =>
          res := IntSet.add(numchild, res^)
        | _ => (),
        constructs,
      );

    List.iter(g, breakdowns);
    List.map(build_child_var, IntSet.elements(res^));
  };

  /*we should probably generate content while we are generating it instead of doing another pass*/
  let collect_freedoms =
      ((_, _, _, _, _, _, breakdowns): rstep_partitioned): list(expr) => {
    let res = ref([]);
    let g = ((_, freedoms, _, _, _, _, _): breakdown_enhanced): _ =>
      res := List.map(((l, _)) => expr_of_intexpr(l), freedoms) @ res^;

    List.iter(g, breakdowns);
    res^;
  };

  let cons_code_of_rstep =
      ((_, _, _, _, _, _, breakdowns): rstep_partitioned): code => {
    let prepare_constructs = (l: list(Spl.spl)): code => {
      let f = e =>
        switch (e) {
        | [@implicit_arity] Spl.Construct(numchild, rs, args, funcs) =>
          [@implicit_arity]
          Assign(
            build_child_var(numchild),
            New(
              [@implicit_arity]
              FunctionCall(
                rs,
                List.map(expr_of_intexpr, args)
                @ List.map(x => New(expr_of_idxfunc(x)), funcs),
              ),
            ),
          )
        | [@implicit_arity]
          Spl.ISumReinitConstruct(numchild, i, count, rs, cold, reinit, funcs) =>
          let child = build_child_var(numchild);
          Chain([
            [@implicit_arity]
            ArrayAllocate(child, Ctype.Env(rs), expr_of_intexpr(count)),
            [@implicit_arity]
            Loop(
              expr_of_intexpr(i),
              expr_of_intexpr(count),
              [@implicit_arity]
              PlacementNew(
                AddressOf(
                  [@implicit_arity]
                  Nth(
                    [@implicit_arity] Cast(child, Ctype.Ptr(Ctype.Env(rs))),
                    expr_of_intexpr(i),
                  ),
                ),
                [@implicit_arity]
                FunctionCall(
                  rs,
                  List.map(expr_of_intexpr, cold @ reinit)
                  @ List.map(x => New(expr_of_idxfunc(x)), funcs),
                ),
              ),
            ),
          ]);
        | _ => failwith("this is not a construct!")
        };

      Chain(List.map(f, l));
    };

    let prepare_precomputations = (a: option(Spl.spl)): code =>
      switch (a) {
      | Some(x) =>
        print_string(
          "Preparing precomputations for : " ++ Spl.string_of_spl(x) ++ "\n",
        );
        Chain([
          [@implicit_arity]
          ArrayAllocate(
            _dat,
            Ctype.Complex,
            expr_of_intexpr(Spl.spl_range(x)),
          ),
          code_of_spl(_dat, _internal_error, x),
        ]);
      | None => Noop
      };

    let rulecount = ref(0);
    let g =
        (
          stmt: code,
          (condition, freedoms, _, _, desc_cons, desc_constructs, _): breakdown_enhanced,
        )
        : code => {
      let freedom_assigns =
        List.map(
          ((l, r)) =>
            [@implicit_arity]
            Assign(expr_of_intexpr(l), expr_of_intexpr(r)),
          freedoms,
        );
      rulecount := rulecount^ + 1;
      [@implicit_arity]
      If(
        [@implicit_arity]
        Var(Ctype.Bool, Boolexpr.string_of_boolexpr(condition)),
        Chain(
          [
            [@implicit_arity]
            Assign(_rule, expr_of_intexpr(Intexpr.IConstant(rulecount^))),
          ]
          @ freedom_assigns
          @ [
            Chain([
              prepare_precomputations(desc_cons),
              prepare_constructs(desc_constructs),
            ]),
          ],
        ),
        stmt,
      );
    };

    List.fold_left(g, ErrorMsg("no applicable rules"), breakdowns);
  };

  let (name, _, cold, reinit, hot, funcs, _) = rstep_partitioned;
  let cons_args =
    List.map(
      expr_of_intexpr,
      IntExprSet.elements(cold) @ IntExprSet.elements(reinit),
    )
    @ List.map(expr_of_idxfunc, funcs);
  let comp_args = [
    _output,
    _input,
    ...List.map(expr_of_intexpr, IntExprSet.elements(hot)),
  ];

  let comp_code_of_rstep =
      (
        (_, _, _, _, _, _, breakdowns): rstep_partitioned,
        output: expr,
        input: expr,
      )
      : code => {
    let rulecount = ref(0);
    let g =
        (stmt: code, (_, _, _, _, _, _, desc_comp): breakdown_enhanced): code => {
      print_string(
        "Preparing computations for : "
        ++ Spl.string_of_spl(desc_comp)
        ++ "\n",
      );
      rulecount := rulecount^ + 1;
      [@implicit_arity]
      If(
        [@implicit_arity]
        Equal(_rule, expr_of_intexpr(Intexpr.IConstant(rulecount^))),
        code_of_spl(output, input, desc_comp),
        stmt,
      );
    };

    List.fold_left(
      g,
      ErrorMsg("internal error: no valid rule has been selected"),
      breakdowns,
    );
  };

  print_string("=== Building " ++ name ++ " ===\n");
  let met =
    [@implicit_arity]
    Method(
      Ctype.Void,
      _compute,
      comp_args,
      comp_code_of_rstep(rstep_partitioned, _output, _input),
    );
  print_string("... built method \n");
  let cons =
    [@implicit_arity]
    Constructor(cons_args, cons_code_of_rstep(rstep_partitioned));
  print_string("... built constructor \n");
  let claz =
    [@implicit_arity]
    Class(
      name,
      _rs,
      [_rule, _dat, ...cons_args]
      @ collect_children(rstep_partitioned)
      @ collect_freedoms(rstep_partitioned),
      [cons, met],
    );
  print_string("... built class \n");
  claz;
};

let code_of_envfunc = ((name, f, args, fargs): envfunc): code => {
  print_string("=== Building " ++ name ++ " ===\n");
  print_string("definition:" ++ Idxfunc.string_of_idxfunc(f) ++ "\n");
  print_string(
    "args:"
    ++ String.concat(", ", List.map(Intexpr.string_of_intexpr, args))
    ++ "\n",
  );
  print_string(
    "fargs:"
    ++ String.concat(", ", List.map(Idxfunc.string_of_idxfunc, fargs))
    ++ "\n",
  );

  let g = ref(f);
  let rankvars = ref([]) /* while (Idxfunc.rank_of_func !g > 0) do */; /* FIXME, there is an issue here, how to handle the rank of these guys? */
  print_string("downranking:" ++ Idxfunc.string_of_idxfunc(g^) ++ "\n");
  let i = Intexpr.gen_loop_counter#get();
  g := Idxfunc.simplify_idxfunc([@implicit_arity] Idxfunc.FDown(g^, i, 0));
  rankvars := [expr_of_intexpr(i), ...rankvars^];
  /* done; */
  let input = gen_var#get(Ctype.Int, "t");
  let (output, code) = code_of_func(g^, (input, []));
  let cons_args =
    List.map(expr_of_intexpr, args) @ List.map(expr_of_idxfunc, fargs);
  [@implicit_arity]
  Class(
    name,
    Idxfunc.ctype_of_func(f),
    cons_args,
    [
      [@implicit_arity] Constructor(cons_args, Noop),
      [@implicit_arity]
      Method(
        Ctype.Complex,
        _at,
        rankvars^ @ [input],
        Chain(code @ [Return(output)]),
      ),
    ],
  );
};

let code_of_lib = ((funcs, rsteps): lib): list(code) =>
  List.map(code_of_envfunc, funcs) @ List.map(code_of_rstep, rsteps);
