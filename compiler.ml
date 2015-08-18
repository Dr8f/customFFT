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
  List.fold_left (fun c (ctype,name) -> substitution_expr_on_code (Var(ctype,name)) (gen_var#get ctype "r") c) code bound_vars
;;

(* lots of missing stuff here *)
let constant_folding : code -> code =
  meta_transform_expr_on_code BottomUp ( function
  | Mul((IConst 0), x) | Mul(x, (IConst 0)) -> IConst 0
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
  let eliminate_within_a_chain (l :code list) : code list =
    let g ((insns, map, set) : code list * expr ExprMap.t  * ExprSet.t) (next_insn:code) : (code list * expr ExprMap.t * ExprSet.t) =
      let rec simplify_expr (expr:expr) (map:expr ExprMap.t) : expr * expr ExprMap.t * code list =
	if (ExprMap.mem expr map) then
	  (ExprMap.find expr map,map, [])
	else
	  match expr with
	    Var _ | IConst _ | Cast _-> (expr,map,[])
	  | Nth(a,b) | Plus(a,b) |Minus(a,b) |Mul(a,b) ->
	     let (na,nmap1,insn1) = (simplify_expr a map) in
	     let (nb,nmap2,insn2) = (simplify_expr b nmap1) in
	     let nexpr = match expr with
	       | Nth _ -> Nth(na,nb)
	       | Plus _ -> Plus(na,nb)
	       | Minus _ -> Minus(na,nb)
	       | Mul _ -> Mul(na,nb)
	     in
	     let (res,insn3) =
	       if (ExprMap.mem nexpr nmap2) then
		 (ExprMap.find nexpr nmap2,[])
	       else
		 let nvar = gen_var#get (ctype_of_expr nexpr) "g" in
		 (nvar, [Declare(nvar);Assign(nvar, nexpr)])
	     in
	     (res, (ExprMap.add nexpr res nmap2), insn1@insn2@insn3)
	  | _ -> failwith("case not handled by simplify_expr : "^(string_of_expr expr))
      in
      match next_insn with
	Declare var -> (* only values actually declared within the scope can be eliminated or replaced, 
                          so we keep track of them *)
 	(insns, map, (ExprSet.add var set))

      (* FIXME no writes are assumed, this would require some invalidation*)
      | Assign(lvalue, rvalue) ->
	 (* first we want to simplify the rvalue if we can *)
	 let (newrvalue,newmap,newinsns) = simplify_expr rvalue map in
	 (match lvalue with
	   Var _ -> 
	     if (ExprSet.mem lvalue set) then
	       (* if the lvalue is a variable declared within the scope, then we can substitute all upcoming iterations*)
	       ((insns@newinsns), ExprMap.add lvalue newrvalue newmap, set)
	     else
	       failwith("Are we really assigning to a variable not declared within the scope??")
	 | Nth(var,idx) ->
	    let (newidx, newmap2, newinsns2) = simplify_expr idx newmap in
	    ((insns@newinsns@newinsns2@[Assign(Nth(var,newidx), newrvalue)]), newmap2, set)
	 | _ ->
	    failwith "what are we assigning to?")
      | _ -> failwith "what is this instruction?"
    in
    let (final, out_map, out_set) = (List.fold_left g ([], ExprMap.empty, ExprSet.empty) l) in
    final
  in
  let f : code -> code = function
      Chain list -> Chain (eliminate_within_a_chain list)
    | x-> x in
  meta_transform_code_on_code BottomUp f (canonical_associative_form code)
;;
		 
let compile_bloc (code:code) : code =
  let compilation_sequence = [unroll_loops; array_scalarization; common_subexpression_elimination] in 
  let f (code:code) (compilation_function:code->code) : code = compilation_function code in
  let res = List.fold_left f code compilation_sequence in 
  print_string(string_of_code 0 code);
  print_string "\n\n => \n\n\n";
  print_string(string_of_code 0 res);
  res
;;
