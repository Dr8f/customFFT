type ctype = 
  Int
| Env of string
| Func of ctype list
| Ptr of ctype
| Char
| Complex
| Void
| Bool
;;

let rec string_of_ctype (t : ctype) : string =
  match t with
  |Int -> "Int"
  |Func(r) -> "Func(["^(String.concat "; " (List.map string_of_ctype r))^"])"
  |Env(rs) -> "Env(\""^rs^"\")"
  |Ptr(ctype)->"Ptr("^(string_of_ctype ctype)^")"
  |Char -> "Char"
  |Complex -> "Complex"
  |Void -> "Void"
  |Bool -> "Bool"
;;

type cvar = string * ctype
;;

let string_of_cvar ((s, ct) : cvar) : string =
  "("^s^", "^(string_of_ctype ct)^")"
;;

let ctype_of_cvar ((_,ct):cvar) : ctype =
  ct
;;

let name_of_cvar ((s,_):cvar) : string =
  s
;;


