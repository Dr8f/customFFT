(******
TYPES
*******)

print_string "= Building the library =\n"
;;

let lib = Lib.make_lib [Spl.DFT(Intexpr.IArg(1))] [Algo.algo_cooley_tukey; Algo.algo_dft_base]
;;

print_string (Lib.string_of_lib lib)
;;

print_string "= Building the code =\n"
;;

let codes = Codegen.code_of_lib lib
;;

print_string "= Unparsing =\n"
;;

let cppcode = (Unparser.string_of_codes 0 codes)
;;

(* print_string cppcode *)
(* ;; *)

let file = "result/result.cpp"

let () =
  let oc = open_out file in
  Printf.fprintf oc "%s\n" cppcode;
  close_out oc;







