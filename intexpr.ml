open Util
;;

type intexpr =
  IConstant of int
| IFreedom of int (* degree of freedom *)
| ILoopCounter of int
| IArg of int (* function argument *)
| IMul of intexpr list
| IPlus of intexpr list
| IDivPerfect of intexpr * intexpr (* IDivPerfect(i,j) = i / j and j divides i for sure *)
| IDivisor of intexpr (* IDivisor(i) returns a divisor of i *)
| ICountWrap of int * intexpr (* internal *)
;;

let rec string_of_intexpr (e : intexpr) : string =
  match e with
    IConstant i -> optional_short_print (string_of_int i) ("IConstant("^(string_of_int i)^")")
  | IMul (l) -> optional_short_infix_list_print "IMul" " * " l string_of_intexpr
  | IPlus (l) -> optional_short_infix_list_print "IPlus" " + " l string_of_intexpr
  | IDivPerfect(l,r) -> optional_short_print ((string_of_intexpr l)^" / "^(string_of_intexpr r)) ("IDivPerfect("^((string_of_intexpr l)^", "^(string_of_intexpr r))^")")
  | ICountWrap (l,r) -> "ICountWrap("^string_of_int l^", "^string_of_intexpr r^")"
  | IDivisor(l)->"IDivisor("^string_of_intexpr l^")"
  | IFreedom i -> optional_short_print ("d"^(string_of_int i)) ("IFreedom("^(string_of_int i)^")")
  | ILoopCounter i -> optional_short_print ("i"^(string_of_int i)) ("ILoopCounter("^(string_of_int i)^")")
  | IArg i -> optional_short_print ("u"^(string_of_int i)) ("IArg("^(string_of_int i)^")")
;;
  
let string_of_intexpr_intexpr ((e,f) : intexpr * intexpr) : string = 
  (string_of_intexpr e)^"="^(string_of_intexpr f)
;;

let string_of_intexpr_intmap (map: intexpr IntMap.t) : string =
  "IntexprIntMap("^(String.concat "; " (List.map (function (e,f)-> "("^(string_of_int e)^", "^(string_of_intexpr f)^")") (IntMap.bindings map)))^")"
;;

let meta_transform_intexpr_on_intexpr (recursion_direction: recursion_direction) (f : intexpr -> intexpr) : (intexpr -> intexpr) = 
  (* print_string "meta_transform_intexpr_on_intexpr\n"; *)
  let z (g : intexpr -> intexpr) (e : intexpr) : intexpr = 
    match e with
    | IMul (l) -> IMul(List.map g l)
    | IPlus (l) -> IPlus(List.map g l)
    | IDivPerfect(a,b) -> IDivPerfect(g a,g b)
    | ICountWrap(a,b) -> e (*FIXME this seems just wrong*)
    | IFreedom _ | IArg _ | IConstant _ | ILoopCounter _ -> e
    | _ -> failwith("meta_transform_intexpr_on_intexpr, not handled: "^(string_of_intexpr e))         		
  in
  recursion_transform recursion_direction f z
;;

let meta_collect_intexpr_on_intexpr (f : intexpr -> 'a list) : (intexpr -> 'a list) =
  let z (g : intexpr -> 'a list) (e : intexpr) : 'a list =
    match e with
    | IMul (l) -> List.flatten (List.map g l)
    | IPlus (l) -> List.flatten (List.map g l)
    | IDivPerfect (a,b) -> (g a)@(g b)
    | IDivisor (l) -> g l
    | _ -> []
  in
  recursion_collect f z
;;

let meta_iter_intexpr_on_intexpr (f : intexpr -> unit) : (intexpr -> unit) =
  fun (e : intexpr) ->
    ignore(meta_collect_intexpr_on_intexpr (fun (e:intexpr) -> f e;[]) e)
;;

let gen_loop_counter =
object 
  val tbl = ref 0;
  method get () : intexpr = 
    tbl := !tbl + 1;
    ILoopCounter !tbl
end
;;

(*********************************************
	 RULES                 
*********************************************)

let meta_multiply_intexpr (recursion_direction : recursion_direction) (f : intexpr list -> intexpr list) : (intexpr -> intexpr) =
  meta_transform_intexpr_on_intexpr recursion_direction ( function 
					       | IMul (l) -> IMul (f l) 
					       | x -> x)
;;

let meta_addition_intexpr (recursion_direction : recursion_direction) (f : intexpr list -> intexpr list) : (intexpr -> intexpr) =
  meta_transform_intexpr_on_intexpr recursion_direction ( function 
					       | IPlus (l) -> IPlus (f l) 
					       | x -> x)
;;

let rule_remove_unary_fmul_on_intexpr : (intexpr -> intexpr) =
  meta_transform_intexpr_on_intexpr BottomUp ( function 
  | IMul ([x]) -> x
  | x -> x)
;;
  
let rule_multiply_by_one_on_intexpr : (intexpr -> intexpr) =
  let rec f (l : intexpr list) : intexpr list =
    match l with
    | IConstant 1 :: tl -> f tl
    | a :: IConstant 1 :: tl -> f (a :: tl)
    | a :: tl -> a :: (f tl)
    | [] -> []
  in
  meta_multiply_intexpr BottomUp f
;;

let rule_addition_zero_on_intexpr : (intexpr -> intexpr) =
  let rec f (l : intexpr list) : intexpr list =
    match l with
    | IConstant 0 :: tl -> f tl
    | a :: IConstant 0 :: tl -> f (a :: tl)
    | a :: tl -> a :: (f tl)
    | [] -> []
  in
  meta_addition_intexpr BottomUp f
;;


let rule_multiply_and_divide_by_the_same_on_intexpr : (intexpr -> intexpr) =
  let rec f (l : intexpr list) : intexpr list = 
    match l with
    | a :: IDivPerfect(b, c) :: tl  when a = c -> f (b::tl)
    | IDivPerfect(a, b) :: c :: tl  when b = c -> f (a::tl)
    | a :: tl -> a :: (f tl)
    | [] -> []
  in
  meta_multiply_intexpr BottomUp f
;;

let intexpr_rulemap = 
    List.fold_left (fun (map) (name, rule) -> StringMap.add name rule map ) StringMap.empty ([
  ("Remove unary fmul", rule_remove_unary_fmul_on_intexpr);
  ("Multiply by one", rule_multiply_by_one_on_intexpr);
  ("Addition zero", rule_addition_zero_on_intexpr);
  ("Multiply and divide by the same", rule_multiply_and_divide_by_the_same_on_intexpr) ])
;;
