open Lib
;;

type ctype = 
  Int
;;

type var = 
|Var of ctype * string
;;

type code =
  Class of string(*name*) * var list(*cold args*) * code (*cons*)
| Chain of code list
| Assign of var * var (* FIXME : should be lvalue and rvalue *)
;;

let code_of_lib (lib : lib) : code = 
  let f ((name, rstep, cold, reinit, hot, breakdowns ) : rstep_partitioned) =
    Class (name, List.map (function x -> Var(Int, Spl.string_of_intexpr x)) (IntExprSet.elements cold), Chain([]))
  in
  Chain (List.map f lib)
;;

