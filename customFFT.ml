(******
TYPES
*******)

let lib = Lib.make_lib [Spl.DFT(Spl.IArg(1))] [Algo.algo_cooley_tukey; Algo.algo_dft_base]
;;

(* print_string (Lib.string_of_lib lib) *)
(* ;; *)

let code = Codegen.code_of_lib lib
;;

(* print_string "********************************\n" *)
(* ;; *)

let cppcode = (Unparser.string_of_code 0 code)
;;

(* print_string cppcode *)
(* ;; *)

let file = "result/result.cpp"

let () =
  let oc = open_out file in
  Printf.fprintf oc "%s\n" cppcode;
  close_out oc;






