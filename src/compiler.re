open Util;

open Ctype;

open Code;

let remove_decls: code => code = (
  meta_transform_code_on_code(
    BottomUp,
    fun
    | Declare(_) => Noop
    | x => x,
  ):
    code => code
);

let replace_bound_vars = (code: code): code => {
  let bound_vars =
    meta_collect_code_on_code(
      fun
      | Declare([@implicit_arity] Var(ctype, name))
      | [@implicit_arity] Loop([@implicit_arity] Var(ctype, name), _, _) => [
          (ctype, name),
        ]
      | _ => [],
      code,
    );
  List.fold_left(
    (c, (ctype, name)) =>
      substitution_expr_on_code(
        [@implicit_arity] Var(ctype, name),
        gen_var#get(ctype, "r"),
        c,
      ),
    code,
    bound_vars,
  );
};

/* lots of missing stuff here */
let constant_folding: code => code = (
  meta_transform_expr_on_code(
    BottomUp,
    fun
    | [@implicit_arity] Mul(IConst(0), _)
    | [@implicit_arity] Mul(_, IConst(0)) => IConst(0)
    | [@implicit_arity] Mul(IConst(1), x)
    | [@implicit_arity] Mul(x, IConst(1)) => x
    | [@implicit_arity] Plus(IConst(0), x)
    | [@implicit_arity] Plus(x, IConst(0)) => x
    | x => x,
  ):
    code => code
);

let unroll_loops = (code: code): code => {
  let unroll_loops_ugly: code => code = (
    meta_transform_code_on_code(
      TopDown,
      fun
      | [@implicit_arity] Loop(var, IConst(n), code) => {
          let g = (i: int) =>
            substitution_expr_on_code(
              var,
              IConst(i),
              replace_bound_vars(code),
            );
          Chain(List.map(g, range(0, n - 1)));
        }
      | x => x,
    ):
      code => code
    /* to avoid multi-declarations of the same variable, we replace bound variables from code */
  );
  flatten_chain(constant_folding(unroll_loops_ugly(code)));
};

let array_scalarization = (code: code): code => {
  let all_arrays =
    meta_collect_code_on_code(
      fun
      | [@implicit_arity] ArrayAllocate(arr, ctype, size) => [
          (arr, ctype, size),
        ]
      | _ => [],
      code,
    );
  let attempt_to_scalarize =
      (code: code, (array, ctype, size): (expr, ctype, expr)): code => {
    let all_nth =
      meta_collect_expr_on_code(
        fun
        | [@implicit_arity] Nth(arr, idx) when arr == array => [idx]
        | _ => [],
        code,
      );
    let nth_consts =
      List.flatten(
        List.map(
          fun
          | IConst(x) => [x]
          | _ => [],
          all_nth,
        ),
      );
    if (List.length(nth_consts) != List.length(all_nth)) {
      code;
    } else {
      let value_set =
        List.fold_left(
          (s, c) => IntSet.add(c, s),
          IntSet.empty,
          nth_consts,
        );
      let h = (i: int, code: code): code => {
        let varname = gen_var#get(ctype, "a");
        let r1 =
          substitution_expr_on_code(
            [@implicit_arity] Nth(array, IConst(i)),
            varname,
            code,
          );
        let r2 = substitution_code_on_code(Declare(array), Noop, r1);
        let r3 =
          substitution_code_on_code(
            [@implicit_arity] ArrayAllocate(array, ctype, size),
            Noop,
            r2,
          );
        let r =
          substitution_code_on_code(
            [@implicit_arity] ArrayDeallocate(array, size),
            Noop,
            r3,
          );
        flatten_chain(Chain([Declare(varname), r]));
      };
      IntSet.fold(h, value_set, code);
    };
  };

  List.fold_left(attempt_to_scalarize, code, all_arrays);
};

let canonical_associative_form: code => code = (
  meta_transform_expr_on_code(
    BottomUp,
    fun
    | [@implicit_arity] Mul(x, y) =>
      if (x < y) {
        [@implicit_arity] Mul(x, y);
      } else {
        [@implicit_arity] Mul(y, x);
      }
    | [@implicit_arity] Plus(x, y) =>
      if (x < y) {
        [@implicit_arity] Plus(x, y);
      } else {
        [@implicit_arity] Plus(y, x);
      }
    | x => x,
  ):
    code => code
);

let common_subexpression_elimination = (code: code): code => {
  let rec eliminate_within_a_chain =
          (map_orig: ExprMap.t(expr), list: list(code)): list(code) => {
    let map = ref(map_orig); /*represents the substitutions to be executed*/
    let output = ref([]);
    let handle = (nexpr: expr): expr =>
      if (ExprMap.mem(nexpr, map^)) {
        ExprMap.find(nexpr, map^);
      } else {
        let nvar = gen_var#get(ctype_of_expr(nexpr), "g");
        output :=
          output^ @ [Declare(nvar), [@implicit_arity] Assign(nvar, nexpr)];
        map := ExprMap.add(nexpr, nvar, map^);
        nvar;
      };
    let rec z = (expr: expr): expr =>
      if (ExprMap.mem(expr, map^)) {
        ExprMap.find(expr, map^);
      } else {
        switch (expr) {
        | Var(_)
        | IConst(_)
        | Cast(_) => expr
        | [@implicit_arity] Plus(a, b) =>
          handle([@implicit_arity] Plus(z(a), z(b)))
        | [@implicit_arity] Minus(a, b) =>
          handle([@implicit_arity] Minus(z(a), z(b)))
        | [@implicit_arity] Mul(a, b) =>
          handle([@implicit_arity] Mul(z(a), z(b)))
        | [@implicit_arity] Nth(a, b) =>
          handle([@implicit_arity] Nth(z(a), z(b)))
        | _ => failwith("case not handled by z : " ++ string_of_expr(expr))
        };
      };
    let process_one_instruction = (next_insn: code): unit =>
      switch (next_insn) {
      | Declare(_) => ()

      | [@implicit_arity] ArrayAllocate(var, ctype, rvalue) =>
        output :=
          output^
          @ [
            Declare(var),
            [@implicit_arity] ArrayAllocate(var, ctype, z(rvalue)),
          ]

      | [@implicit_arity] ArrayDeallocate(var, rvalue) =>
        output :=
          output^ @ [[@implicit_arity] ArrayDeallocate(var, z(rvalue))]

      | [@implicit_arity] Loop(var, count, Chain(code)) =>
        output :=
          output^
          @ [
            [@implicit_arity]
            Loop(
              var,
              z(count),
              Chain(eliminate_within_a_chain(map^, code)),
            ),
          ]

      | Chain(x) =>
        output := output^ @ [Chain(eliminate_within_a_chain(map^, x))]

      /* the following assumes no writes are really needed, except those in memory*/
      | [@implicit_arity] Assign(Var(_) as lvalue, rvalue) =>
        map := ExprMap.add(lvalue, z(rvalue), map^)

      | [@implicit_arity] Assign([@implicit_arity] Nth(a, b), rvalue) =>
        output :=
          output^
          @ [
            [@implicit_arity]
            Assign([@implicit_arity] Nth(z(a), z(b)), z(rvalue)),
          ]

      | _ =>
        failwith(
          "what is this instruction? " ++ string_of_code(0, next_insn),
        )
      };

    List.iter(process_one_instruction, list);
    output^;
  };

  switch (canonical_associative_form(code)) {
  | Chain(list) => Chain(eliminate_within_a_chain(ExprMap.empty, list))
  | _ => failwith("not supported")
  };
};

let compile_bloc = (code: code): code => {
  let compilation_sequence = [
    unroll_loops,
    array_scalarization,
    common_subexpression_elimination,
  ];
  let f = (code: code, compilation_function: code => code): code =>
    compilation_function(code);
  let res = List.fold_left(f, code, compilation_sequence);
  /* print_string(string_of_code 0 code); */
  /* print_string "\n\n => \n\n\n"; */
  /* print_string(string_of_code 0 res); */
  res;
};
