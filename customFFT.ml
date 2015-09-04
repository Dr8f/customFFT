(******
TYPES
*******)

(* print_string "= Building the library =\n" *)
(* ;; *)

(* let lib = Lib.make_lib [Spl.DFT(Intexpr.IArg(1))] [Algo.algo_cooley_tukey; Algo.algo_dft_base] *)
(* ;; *)

(* print_string (Lib.string_of_lib lib) *)
(* ;; *)

(* print_string "= Building the code =\n" *)
(* ;; *)

(* let codes = Codegen.code_of_lib lib *)
(* ;; *)

(* print_string "= Unparsing =\n" *)
(* ;; *)

(* let cppcode = (Unparser.string_of_codes 0 codes) *)
(* ;; *)

(* (\* print_string cppcode *\) *)
(* (\* ;; *\) *)

(* let file = "result/result.cpp" *)

(* let () = *)
(*   let oc = open_out file in *)
(*   Printf.fprintf oc "%s\n" cppcode; *)
(*   close_out oc; *)


open Spl
;;

let myrule : spl -> spl = 
  let f (s:spl) (ctx:spl list) : spl =
    print_string ("Applying the local rule to "^(string_of_spl s)^" Context is ["^(String.concat ", " (List.map string_of_spl ctx))^"]\n");
    match s with 
    | T(n,k) -> Diag(Pre(FD(n,k)))
    | x -> x
  in
  meta_transform_spl_on_spl_context TopDown f
;;

let my_in = RS(RS(T(IConstant 1, IConstant 3))) in
    let z = myrule (my_in) in
    z
;;



