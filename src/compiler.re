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
      | Declare(Var(ctype, name))
      | Loop(Var(ctype, name), _, _) => [
          (ctype, name),
        ]
      | _ => [],
      code,
    );
  List.fold_left(
    (c, (ctype, name)) =>
      substitution_expr_on_code(
        Var(ctype, name),
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
    | Mul(IConst(0), _)
    | Mul(_, IConst(0)) => IConst(0)
    | Mul(IConst(1), x)
    | Mul(x, IConst(1)) => x
    | Plus(IConst(0), x)
    | Plus(x, IConst(0)) => x
    | x => x,
  ):
    code => code
);

let unroll_loops = (code: code): code => {
  let unroll_loops_ugly: code => code = (
    meta_transform_code_on_code(
      TopDown,
      fun
      | Loop(var, IConst(n), code) => {
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
      | ArrayAllocate(arr, ctype, size) => [
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
        | Nth(arr, idx) when arr == array => [idx]
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
            Nth(array, IConst(i)),
            varname,
            code,
          );
        let r2 = substitution_code_on_code(Declare(array), Noop, r1);
        let r3 =
          substitution_code_on_code(
            ArrayAllocate(array, ctype, size),
            Noop,
            r2,
          );
        let r =
          substitution_code_on_code(
            ArrayDeallocate(array, size),
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
    | Mul(x, y) =>
      if (x < y) {
        Mul(x, y);
      } else {
        Mul(y, x);
      }
    | Plus(x, y) =>
      if (x < y) {
        Plus(x, y);
      } else {
        Plus(y, x);
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
          output^ @ [Declare(nvar), Assign(nvar, nexpr)];
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
        | Plus(a, b) =>
          handle(Plus(z(a), z(b)))
        | Minus(a, b) =>
          handle(Minus(z(a), z(b)))
        | Mul(a, b) =>
          handle(Mul(z(a), z(b)))
        | Nth(a, b) =>
          handle(Nth(z(a), z(b)))
        | _ => failwith("case not handled by z : " ++ string_of_expr(expr))
        };
      };
    let process_one_instruction = (next_insn: code): unit =>
      switch (next_insn) {
      | Declare(_) => ()

      | ArrayAllocate(var, ctype, rvalue) =>
        output :=
          output^
          @ [
            Declare(var),
            ArrayAllocate(var, ctype, z(rvalue)),
          ]

      | ArrayDeallocate(var, rvalue) =>
        output :=
          output^ @ [ArrayDeallocate(var, z(rvalue))]

      | Loop(var, count, Chain(code)) =>
        output :=
          output^
          @ [
            Loop(
              var,
              z(count),
              Chain(eliminate_within_a_chain(map^, code)),
            ),
          ]

      | Chain(x) =>
        output := output^ @ [Chain(eliminate_within_a_chain(map^, x))]

      /* the following assumes no writes are really needed, except those in memory*/
      | Assign(Var(_) as lvalue, rvalue) =>
        map := ExprMap.add(lvalue, z(rvalue), map^)

      | Assign(Nth(a, b), rvalue) =>
        output :=
          output^
          @ [
            Assign(Nth(z(a), z(b)), z(rvalue)),
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
