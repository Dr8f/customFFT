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

let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: t -> last t;;

let drop_last (l:'a list) =
  match List.rev l with
  | [] -> failwith("could not be inverted, was empty")
  | _ ::t -> List.rev t
  
(*********************************************
	 RECURSION SUPPORT
*********************************************)

type recursion_direction = 
  BottomUp 
| TopDown
;;

let recursion_transform (recursion_direction: recursion_direction) (z : ('a -> 'a) -> 'a -> 'a) (f : 'a -> 'a) : ('a -> 'a) =
  let rec g (e : 'a) : 'a =
    let s = z g in
    match recursion_direction with
    | BottomUp -> f (s e)
    | TopDown -> s (f e)
  in g
;;

let recursion_transform_ctx (recursion_direction: recursion_direction) (z : ('a -> 'a) -> 'a list -> 'a -> 'a) (f : 'a list -> 'a -> 'a) : ('a -> 'a) =
  let rec g (ctx:'a list) (e : 'a) : 'a =
    let s = z (fun a -> g (e::ctx) a) ctx in
    match recursion_direction with
    | BottomUp -> f ctx (s e)
    | TopDown -> s (f ctx e)
  in g []
;;

  
let recursion_collect (z : ('a -> 'b list) -> 'a -> 'b list) (f : 'a -> 'b list) : ('a -> 'b list) =
  let rec g (e : 'a) : 'b list =
    f e @ (z g e)
  in
  g
;;

let recursion_collect_ctx (z : ('a -> 'b list) -> 'a list -> 'a -> 'b list) (f : 'a list -> 'a -> 'b list) : ('a -> 'b list) =
  let rec g (ctx:'a list) (e : 'a) : 'b list =
    let s = z (fun a -> g (e::ctx) a) ctx in
    f ctx e @ (s e)
  in
  g []
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
    let f (_:string) (rule : 'a -> 'a) (e : 'a) : 'a=
(*      if (e <> outcome) then print_endline ("===  " ^ name ^ "  ===\n    " ^ (string_of_'a e) ^ "\n    " ^ (string_of_spl outcome) ^ "\n") ;  *)
      rule e
    in
    StringMap.fold f rules e
  in
  let next = apply_rewriting_rules_once e in
  if (e = next) then e else (apply_rewriting_rules rules next)
;;
