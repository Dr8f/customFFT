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
  
let rec unroll_loops (code:code) : code =
  flatten_chain (meta_transform_code_on_code TopDown ( function 
  | Loop(var, Const n, code) ->
     let g (i:int) =
       (* to avoid multi-declarations of the same variable, we replace bound variables from code *)
       expr_substitution_on_code var (Const i) (replace_bound_vars code) in
    Chain (List.map g (range 0 (n-1)))
  | x -> x
  ) code )
;;

(* let declare_free_vars (l: code list) : code list = *)
(*   let filter_vars (expr: expr) : expr list = *)
(*     match expr with *)
(*       Var _ -> [expr] *)
(*     | _ -> [] *)
(*   in *)
(*   let vars = meta_collect_expr_on_code filter_vars (Chain l) in *)
(*   let varsset = List.fold_left (fun set elem -> ExprSet.add elem set) ExprSet.empty vars in *)

(*   let f (expr:expr) (str:string) : string = *)
(*     (string_of_expr expr)^" | "^str in *)
(*   print_string (ExprSet.fold f varsset ""); (\*FIXME*\) *)
(*   (\* compute all free variables *\) *)
(*   (\* declare all free variables *\) *)
(*   [] *)
(* ;; *)

(* let rec reintroduce_decls : (code -> code) = *)
(*   meta_transform_code_on_code BottomUp ( function  *)
(*   | Chain (l) -> let decls = declare_free_vars l in Chain (decls @ l)  *)
(*   | x -> x) *)
(* ;; *)

let compile_bloc (code:code) : code =
  (*  let compilation_sequence = [remove_decls;flatten_chain;reintroduce_decls] in*)
  let compilation_sequence = [unroll_loops;(*immediate_arithmetic*)] in 
  let f (code:code) (compilation_function:code->code) : code = compilation_function code in
  let res = List.fold_left f code compilation_sequence in 
  print_string(string_of_code 0 code);
  print_string "\n\n => \n\n\n";
  print_string(string_of_code 0 res);
  res
;;
