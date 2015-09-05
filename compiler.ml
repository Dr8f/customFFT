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
  | Declare _ -> Noop
  | x -> x
  )
;;

let replace_bound_vars (code:code) : code =
  let bound_vars =
    meta_collect_code_on_code ( function
      Declare(Var(ctype,name)) | Loop(Var(ctype,name),_,_) -> [(ctype,name)]
      | _ -> []) code in
  List.fold_left (fun c (ctype,name) -> substitution_expr_on_code (Var(ctype,name)) (gen_var#get ctype "r") c) code bound_vars
;;

(* lots of missing stuff here *)
let constant_folding : code -> code =
  meta_transform_expr_on_code BottomUp ( function
  | Mul((IConst 0), _) | Mul(_, (IConst 0)) -> IConst 0
  | Mul((IConst 1), x) | Mul(x, (IConst 1)) -> x
  | Plus((IConst 0), x) | Plus(x, (IConst 0)) -> x						 
  | x -> x)
;;

let unroll_loops (code:code) : code =
  let unroll_loops_ugly : code -> code =
    meta_transform_code_on_code TopDown ( function 
        | Loop(var, IConst n, code) ->
	   let g (i:int) =
	     (* to avoid multi-declarations of the same variable, we replace bound variables from code *)
	     substitution_expr_on_code var (IConst i) (replace_bound_vars code) in
	   Chain (List.map g (range 0 (n-1)))
	| x -> x) in
  flatten_chain (constant_folding (unroll_loops_ugly code))
;;
  
let array_scalarization (code:code) : code =
  let all_arrays =
    meta_collect_code_on_code ( function
				  ArrayAllocate(arr, ctype, size) -> [(arr, ctype, size)]
				| _ -> []) code in
  let attempt_to_scalarize (code:code) ((array,ctype,size):expr*ctype*expr) : code =
    let all_nth = meta_collect_expr_on_code (function
      | Nth(arr, idx) when arr = array -> [idx]
      | _ -> []) code in
    let nth_consts = List.flatten (List.map (function
				   | (IConst x) -> [x]
				   | _ -> [] ) all_nth) in
    if (List.length nth_consts <> List.length all_nth) then
      code
    else (
      let value_set = List.fold_left (fun s c -> IntSet.add c s) IntSet.empty nth_consts in
      let h (i:int) (code:code) : code =
	let varname = (gen_var#get ctype "a") in
	let r1 = substitution_expr_on_code (Nth(array, (IConst i))) varname code in
	let r2 = substitution_code_on_code (Declare array) Noop r1 in
	let r3 = substitution_code_on_code (ArrayAllocate(array,ctype, size)) Noop r2 in
	let r = substitution_code_on_code (ArrayDeallocate(array,size)) Noop r3 in
	flatten_chain (Chain [Declare(varname); r]) in
      IntSet.fold h value_set code)
  in
  List.fold_left attempt_to_scalarize code all_arrays
;;

let canonical_associative_form : code -> code =
  meta_transform_expr_on_code BottomUp ( function
  | Mul(x, y) -> if (x<y) then Mul(x, y) else Mul(y,x)
  | Plus(x, y) -> if (x<y) then Plus(x, y) else Plus(y,x)
  | x -> x)
;;
  
let common_subexpression_elimination (code:code) : code = 
  let rec eliminate_within_a_chain (map_orig:expr ExprMap.t) (list:code list): code list =
    let map = ref map_orig in (*represents the substitutions to be executed*)
    let output = ref [] in
    let handle (nexpr:expr) : expr =
      if (ExprMap.mem nexpr !map) then 
	ExprMap.find nexpr !map 
      else (
	let nvar = gen_var#get (ctype_of_expr nexpr) "g" in
	output:= (!output)@[Declare(nvar);Assign(nvar, nexpr)];
	map := ExprMap.add nexpr nvar !map;	
	nvar
      ) in
    let rec z (expr:expr) : expr =
      if (ExprMap.mem expr !map) then
	ExprMap.find expr !map
      else
	match expr with
	| Var _ | IConst _ | Cast _-> expr
	| Plus(a, b) -> handle (Plus(z a, z b))
	| Minus(a, b) -> handle (Minus(z a, z b))
	| Mul(a, b) -> handle (Mul(z a, z b))
	| Nth(a, b) -> handle (Nth(z a, z b))
	| _ -> failwith("case not handled by z : "^(string_of_expr expr)) in
    let process_one_instruction (next_insn:code) : unit =
      match next_insn with
      | Declare _ ->
	 ()

      | ArrayAllocate(var, ctype, rvalue) ->
	 output := (!output)@[Declare(var);ArrayAllocate(var, ctype, (z rvalue))] 
	   
      | ArrayDeallocate(var, rvalue) ->
	 output:=(!output)@([ArrayDeallocate(var, (z rvalue))])
	     
      | Loop (var,count,Chain code) ->
	 output:=(!output)@([Loop(var, (z count), Chain(eliminate_within_a_chain !map code))])
	   
      | Chain x ->
	 output:=(!output)@([Chain(eliminate_within_a_chain !map x)])

      (* the following assumes no writes are really needed, except those in memory*)
      | Assign(Var _ as lvalue, rvalue) ->
	 map:=ExprMap.add lvalue (z rvalue) !map	

      | Assign(Nth(a, b), rvalue) ->
	 output:=(!output)@([Assign(Nth(z a, z b),(z rvalue))])
						 
      | _ ->
	 failwith ("what is this instruction? "^(string_of_code 0 next_insn)) 
    in
    List.iter process_one_instruction list;
    !output
  in
  match (canonical_associative_form code) with
  | Chain list -> Chain(eliminate_within_a_chain ExprMap.empty list)
  | _ -> failwith("not supported")
;;
		 
let compile_bloc (code:code) : code =
  let compilation_sequence = [unroll_loops; array_scalarization; common_subexpression_elimination] in  
  let f (code:code) (compilation_function:code->code) : code = compilation_function code in
  let res = List.fold_left f code compilation_sequence in 
  (* print_string(string_of_code 0 code); *)
  (* print_string "\n\n => \n\n\n"; *)
  (* print_string(string_of_code 0 res); *)
  res
;;
