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
  let rec g (e : 'a) : 'a =
    match recursion_direction with
      BottomUp -> f (z g e)
    | TopDown -> z g (f e)
  in
  g  
;;

let recursion_collect (f : 'a -> 'b list) (z : ('a -> 'b list) -> 'a -> 'b list) : ('a -> 'b list) =
  let rec g (e : 'a) : 'b list =
    f e @ (z g e)
  in
  g
;;
