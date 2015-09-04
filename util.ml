module StringMap = Map.Make(String)
;;

module IntMap = Map.Make(struct type t = int let compare = compare end)
;;

module IntSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = int
  end )
;;

let rec white (n:int) : string =
  if (n <= 0) then
    ""
  else
    " "^(white (n-1))
;;

let rec range i j = if i > j then [] else i :: (range (i+1) j)
;;

(*********************************************
	 RECURSION SUPPORT
*********************************************)

type recursion_direction = 
  BottomUp 
| TopDown
;;

let recursion_transform (recursion_direction: recursion_direction) (f : 'a -> 'a) (z : ('a -> 'a) -> 'a -> 'a) : ('a -> 'a) =
  match recursion_direction with
  | BottomUp -> let rec g (e : 'a) : 'a = f (z g e) in g
  | TopDown -> let rec g (e : 'a) : 'a = z g (f e) in g							
;;
  
let recursion_collect (f : 'a -> 'b list) (z : ('a -> 'b list) -> 'a -> 'b list) : ('a -> 'b list) =
  let rec g (e : 'a) : 'b list =
    f e @ (z g e)
  in
  g
;;

(*********************************************
	 PRINTING
*********************************************)
let optional_short_print (short : string) (long : string) : string = 
  let short_print = true in
  if (short_print) then
    short
  else
    long
;;

let optional_short_infix_list_print (name:string) (infix:string) (l:'a list) (f:'a -> string) =
  optional_short_print (String.concat infix (List.map f l)) (name^"(["^(String.concat "; " (List.map f l))^"])")
;;

(*********************************************
	 APPLYING RULES
*********************************************)

let rec apply_rewriting_rules (rules:('a -> 'a) StringMap.t) (e : 'a) : 'a = 
  let apply_rewriting_rules_once (e : 'a) : 'a = 
    let f (name:string) (rule : 'a -> 'a) (e : 'a) : 'a=
(*      if (e <> outcome) then print_endline ("===  " ^ name ^ "  ===\n    " ^ (string_of_'a e) ^ "\n    " ^ (string_of_spl outcome) ^ "\n") ;  *)
      rule e
    in
    StringMap.fold f rules e
  in
  let next = apply_rewriting_rules_once e in
  if (e = next) then e else (apply_rewriting_rules rules next)
;;
