(******
TYPES
*******)

let lib = Lib.make_lib [Spl.DFT(Spl.IArg(1))] Algo.algo_cooley_tukey
;;

print_string (Lib.string_of_lib lib)
;;

print_string (Unparser.string_of_lib lib)
;;
  






