open Util
;;

open Intexpr
;;

type boolexpr =
  IsPrime of intexpr 
| And of boolexpr list
| Equal of intexpr * intexpr
| True
| Not of boolexpr
;;

let rec string_of_boolexpr (e : boolexpr) : string = 
  match e with
    IsPrime(l)->"IsPrime("^string_of_intexpr l^")"
  | And(l)->optional_short_infix_list_print "And" " && " l string_of_boolexpr
  | Equal(a,b)->optional_short_print ("("^string_of_intexpr a^" == "^string_of_intexpr b^")") ("Equal("^string_of_intexpr a^", "^string_of_intexpr b^")")
  | Not(b) -> optional_short_print ("!"^(string_of_boolexpr b)) ("Not("^(string_of_boolexpr b)^")")
  | True->"True"
;;

let meta_collect_boolexpr_on_boolexpr (f : boolexpr -> 'a list) : (boolexpr -> 'a list) =
  let z (g : boolexpr -> 'a list) (e : boolexpr) : 'a list =
    match e with
    | And (l) -> List.flatten (List.map g l)
    | Not(b) -> g b
    | _ -> []
  in
  recursion_collect z f
;;

let meta_collect_intexpr_on_boolexpr (f : intexpr -> 'a list) : (boolexpr -> 'a list) = 
  meta_collect_boolexpr_on_boolexpr ( function
  | IsPrime x -> f x
  | _ -> []
  )
;;

let meta_iter_intexpr_on_boolexpr (f : intexpr -> unit) : (boolexpr -> unit) =
  fun (e : boolexpr) ->
    ignore(meta_collect_intexpr_on_boolexpr (fun (e:intexpr) -> f e;[]) e)
;;
