open Util
;;
open Code
;;


let meta_chain_code (recursion_direction: recursion_direction) (f : code list -> code list) : (code -> code) =
  meta_transform_code_on_code recursion_direction ( function 
  | Chain (l) -> Chain (f l) 
  | x -> x)
;;

let flatten_chain : (code -> code) =
  let rec f (l : code list) : code list = 
  match l with
  | Chain(a)::tl -> f (a @ tl)
  | Noop::tl -> f(tl)
  | a::tl -> a :: (f tl)
  | [] -> []
  in
  meta_chain_code BottomUp f
;;  

let remove_decls : (code -> code) =
  meta_transform_code_on_code BottomUp ( function
  | Declare x -> Noop
  | x -> x
  )
;;

let replace_bound_vars (code:code) : code =
  let bound_vars =
    meta_collect_code_on_code ( function
      Declare(Var(ctype,name)) | Loop(Var(ctype,name),_,_) -> [(ctype,name)]
      | _ -> []) code in
  List.fold_left (fun c (ctype,name) -> expr_substitution_on_code (Var(ctype,name)) (gen_var#get ctype "r") c) code bound_vars
;;

let constant_folding : code -> code =
  meta_transform_expr_on_code BottomUp ( function
  | Mul((Const 0), x) | Mul(x, (Const 0)) -> Const 0
  | Mul((Const 1), x) | Mul(x, (Const 1)) -> x
  | Plus((Const 0), x) | Plus(x, (Const 0)) -> x						 
  | x -> x)
;;

let unroll_loops (code:code) : code =
  let unroll_loops_ugly : code -> code =
    meta_transform_code_on_code TopDown ( function 
        | Loop(var, Const n, code) ->
	   let g (i:int) =
	     (* to avoid multi-declarations of the same variable, we replace bound variables from code *)
	     expr_substitution_on_code var (Const i) (replace_bound_vars code) in
	   Chain (List.map g (range 0 (n-1)))
	| x -> x) in
  flatten_chain (constant_folding (unroll_loops_ugly code))

let array_scalarization (code:code) : code =
  let all_arrays =
    meta_collect_code_on_code ( function
				  ArrayAllocate(arr, ctype, size) -> [(arr, ctype)]
				| _ -> []) code in
  let attempt_to_scalarize (code:code) ((array,ctype):expr*ctype) : code =
    let all_nth = meta_collect_expr_on_code (function
      | Nth(arr, idx) when arr = array -> [idx]
      | _ -> []) code in
    let nth_consts = List.flatten (List.map (function
				   | (Const x) -> [x]
				   | _ -> [] ) all_nth) in
    if (List.length nth_consts <> List.length all_nth) then
      code
    else (
      let value_set = List.fold_left (fun s c -> IntSet.add c s) IntSet.empty nth_consts in
      let h (i:int) (code:code) : code =
	let varname = (gen_var#get ctype "a") in
	let r1 = expr_substitution_on_code (Nth(array, (Const i))) varname code in
	let r = meta_transform_code_on_code BottomUp ( function
						         Declare(arr) when arr = array -> Noop
						       | ArrayAllocate(arr, ct, _) when ((arr = array) & (ct = ctype)) -> Noop
						       | ArrayDeallocate(arr, _) when arr = array -> Noop
						       | x -> x) r1 in
	flatten_chain (Chain [Declare(varname); r]) in
      IntSet.fold h value_set code
  in
  List.fold_left attempt_to_scalarize code all_arrays
  

let compile_bloc (code:code) : code =
  let compilation_sequence = [unroll_loops; array_scalarization] in 
  let f (code:code) (compilation_function:code->code) : code = compilation_function code in
  let res = List.fold_left f code compilation_sequence in 
  print_string(string_of_code 0 code);
  print_string "\n\n => \n\n\n";
  print_string(string_of_code 0 res);
  res
;;
