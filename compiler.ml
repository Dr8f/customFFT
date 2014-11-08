open Util
;;
open Code
;;


let meta_chain_code (recursion_direction: recursion_direction) (f : code list -> code list) : (code -> code) =
  meta_transform_code_on_code recursion_direction ( function 
  | Chain (l) -> Chain (f l) 
  | x -> x)
;;

let rule_flatten_chain : (code -> code) =
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

(* FIXME write the code *)
let rec flatten_chain (code:code) : code =
  rule_flatten_chain (remove_decls code) 
;;

(* takes the code into a multidecl form*)
let rec unroll_loops (code:code) : code =
  meta_transform_code_on_code TopDown ( function 
  | Loop(var, Const n, c) -> 
    let g (i:int) = expr_substitution_on_code var (Const i) c in
    Chain (List.map g (range 0 (n-1)))
  | x -> x
  ) code
;;

let declare_free_vars (l: code list) : code list =
  (* compute all free variables *)
  (* declare all free variables *)
  l
;;

let rec reintroduce_decls : (code -> code) =
  meta_transform_code_on_code BottomUp ( function 
  | Chain (l) -> let decls = declare_free_vars l in Chain (decls @ l) 
  | x -> x)
;;

let compile_bloc (code:code) : code = 
  let res = code in (* flatten_chain (unroll_loops code) in *)
  print_string(string_of_code 0 res);
  print_string "\n\n\n\n\n";
  res
;;
