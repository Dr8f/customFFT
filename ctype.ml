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
