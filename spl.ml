open Util
;;

(*********************************************
	 TYPES
*********************************************)


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

type boolexpr =
  IsPrime of intexpr 
| And of boolexpr list
| Equal of intexpr * intexpr
| True
| Not of boolexpr
;;

type idxfunc = 
  FH of intexpr * intexpr * intexpr * intexpr
(* FH(domain, range, base, stride) maps I(src) to I(dest) so that FH(d,r,b,s)(i) = b + i*s *)
| FL of intexpr * intexpr
| FD of intexpr * intexpr
(* FD(n,k) maps I(n) to a diag of w(n, - 0*0) ... w(n, - (k-1)*0) w(n, - 0*1) ... w(n, - (k-1)*1) ... ... w(n, - (k-1) * (n/k-1)) where w(n, x) = exp(2 Pi * I * x /n) *)
(* thus FD(n,k)(i) = w(n, -(i mod k) * (i\k)) *)
| FCompose of idxfunc list
| Pre of idxfunc (* Precompute *)
| PreWrap of string * intexpr list * idxfunc list * intexpr (*domain*)
| FArg of string * intexpr (*domain*)
| FHH of intexpr * intexpr * intexpr * intexpr * intexpr list
(* FHH(domain, range, base, stride0, vector strides) maps Z**k x I(str) to I(dest) so FHH(d,r,b,s,vs)(j_k .. j_1, i) = b + i*s + Sum j_k * vs_k*)
| FUp of idxfunc
| FDown of idxfunc * intexpr * int
;;

type spl =
DFT of intexpr
| RS of spl (* Recursion step *)
| Tensor of spl list
| I of intexpr
| T of intexpr * intexpr
| L of intexpr * intexpr
| Compose of spl list
| S of idxfunc
| G of idxfunc
| Diag of idxfunc
| ISum of intexpr * intexpr * spl
| UnpartitionnedCall of string * intexpr IntMap.t * idxfunc list * intexpr * intexpr
| PartitionnedCall of int * string * intexpr list * intexpr list * intexpr list * idxfunc list * intexpr * intexpr
| Construct of int * string * intexpr list * idxfunc list
| ISumReinitConstruct of int * intexpr * intexpr * string * intexpr list * intexpr list * idxfunc list
| Compute of int * string * intexpr list * intexpr * intexpr
| ISumReinitCompute of int * intexpr * intexpr * string * intexpr list * intexpr * intexpr
| F of int
| BB of spl
| GT of spl * idxfunc * idxfunc * intexpr list
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

(* let optional_short_infix_list_print (name:string) (l:intexpr list) (infix:string) = *)
(*   optional_short_print (String.concat infix (List.map string_of_intexpr l)) (name^"(^"(string_of_intexpr_list l)"^)") *)
(* ;; *)

let optional_short_infix_list_print (name:string) (infix:string) (l:'a list) (f:'a -> string) =
  optional_short_print (String.concat infix (List.map f l)) (name^"(["^(String.concat "; " (List.map f l))^"])")
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

let rec string_of_boolexpr (e : boolexpr) : string = 
  match e with
    IsPrime(l)->"IsPrime("^string_of_intexpr l^")"
  | And(l)->optional_short_infix_list_print "And" " && " l string_of_boolexpr
  | Equal(a,b)->optional_short_print ("("^string_of_intexpr a^" == "^string_of_intexpr b^")") ("Equal("^string_of_intexpr a^", "^string_of_intexpr b^")")
  | Not(b) -> optional_short_print ("!"^(string_of_boolexpr b)) ("Not("^(string_of_boolexpr b)^")")
  | True->"True"
;;

let string_of_intexpr_intexpr ((e,f) : intexpr * intexpr) : string = 
  (string_of_intexpr e)^"="^(string_of_intexpr f)
;;

let string_of_intexpr_intmap (map: intexpr IntMap.t) : string =
  "IntexprIntMap("^(String.concat "; " (List.map (function (e,f)-> "("^(string_of_int e)^", "^(string_of_intexpr f)^")") (IntMap.bindings map)))^")"
;;

let rec string_of_idxfunc (e : idxfunc) : string =
  match e with
    FH(src, dest, j,k) -> "FH("^(string_of_intexpr src)^","^(string_of_intexpr dest)^","^(string_of_intexpr j)^","^(string_of_intexpr k)^")"
  | FL(j,k) -> "FL("^(string_of_intexpr j)^","^(string_of_intexpr k)^")"      
  | FD(n,k) -> "FD("^(string_of_intexpr n)^","^(string_of_intexpr k)^")"      
  | FCompose(l) -> optional_short_infix_list_print "FCompose" " . " l string_of_idxfunc

  | Pre(l) -> "Pre("^(string_of_idxfunc l)^")"
  | PreWrap(n, l, funcs, d) -> "PreWrap(\""^n^"\", ["^(String.concat "; " (List.map string_of_intexpr l))^"], ["^(String.concat "; " (List.map string_of_idxfunc funcs))^"], "^(string_of_intexpr d)^")"
  | FArg(n, d) -> "FArg(\""^n^"\", "^(string_of_intexpr d)^")"
;;

let rec string_of_spl (e : spl) : string =
  match e with
    DFT (n) -> "DFT("^(string_of_intexpr n)^")"
  | Tensor (list) -> optional_short_infix_list_print "Tensor" " x " list string_of_spl
  | I (n) -> "I("^(string_of_intexpr n)^")"
  | T (n, m) -> "T("^(string_of_intexpr n)^","^(string_of_intexpr m)^")"
  | L (n, m) -> "L("^(string_of_intexpr n)^","^(string_of_intexpr m)^")"
  | Compose (list) -> optional_short_infix_list_print "Compose" " . " list string_of_spl
  | S (f) -> "S("^(string_of_idxfunc f)^")"
  | G (f) -> "G("^(string_of_idxfunc f)^")"
  | Diag (f) -> "Diag("^(string_of_idxfunc f)^")"
  | ISum (i, high, spl) -> "ISum("^(string_of_intexpr i)^","^(string_of_intexpr high)^","^(string_of_spl spl)^")"
  | RS(spl) -> "RS("^(string_of_spl spl)^")"
  | UnpartitionnedCall(f, map, funcs, r, d) -> 
    "UnpartitionnedCall(\""^f^"\", ("^(string_of_intexpr_intmap(map))^"), ["^(String.concat "; " (List.map string_of_idxfunc funcs))^"], "^(string_of_intexpr r)^", "^(string_of_intexpr d)^")"
  | PartitionnedCall(childcount, f, cold, reinit, hot, funcs, r, d) -> 
    "PartitionnedCall("^(string_of_int childcount)^", \""^f^"\", ["^(String.concat ";" (List.map string_of_intexpr cold))^"], ["^(String.concat ";" (List.map string_of_intexpr reinit))^"], ["^(String.concat ";" (List.map string_of_intexpr hot))^"], ["^(String.concat ";" (List.map string_of_idxfunc funcs))^"], "^(string_of_intexpr r)^", "^(string_of_intexpr d)^")"
  | Construct(childcount, f, cold, funcs) -> "Construct("^(string_of_int childcount)^", \""^f^"\", ["^(String.concat ";" (List.map string_of_intexpr cold))^"], ["^(String.concat ";" (List.map string_of_idxfunc funcs))^"])"
  | ISumReinitConstruct(childcount, i, high, f, cold, reinit, funcs) -> "ISumReinitConstruct("^(string_of_int childcount)^", "^(string_of_intexpr i)^", "^(string_of_intexpr high)^", \""^f^"\", ["^(String.concat ";" (List.map string_of_intexpr cold))^"], ["^(String.concat ";" (List.map string_of_intexpr reinit))^"], ["^(String.concat ";" (List.map string_of_idxfunc funcs))^"])"
  | Compute(childcount, f, hot,_,_) ->"Compute("^(string_of_int childcount)^", "^f^", ["^(String.concat ";" (List.map string_of_intexpr hot))^"])"
  | ISumReinitCompute(childcount, i, high, f, hot, _, _) -> "ISumReinitCompute("^(string_of_int childcount)^", "^(string_of_intexpr i)^", "^(string_of_intexpr high)^", "^f^", ["^(String.concat ";" (List.map string_of_intexpr hot))^"])"
  | F(i) -> "F("^(string_of_int i)^")"
  | BB(x) ->"BB("^(string_of_spl x)^")"
;;




(*********************************************
	 METARULES                 
*********************************************)

let meta_transform_spl_on_spl (recursion_direction: recursion_direction) (f : spl -> spl) : (spl -> spl) =
  let z (g : spl -> spl) (e : spl) : spl = 
    match e with
    | Compose (l) -> Compose (List.map g l)
    | Tensor (l) -> Tensor (List.map g l)
    | ISum(v,c,a) -> ISum(v,c, (g a))
    | RS (l) -> RS(g l)
    | BB (l) -> BB(g l)
    | _ -> e          
  in
  recursion_transform recursion_direction f z
;;

let meta_transform_idxfunc_on_idxfunc (recursion_direction: recursion_direction) (f : idxfunc -> idxfunc) : (idxfunc -> idxfunc) =
  let z (g : idxfunc -> idxfunc) (e : idxfunc) : idxfunc = 
    match e with 
    | FCompose (l) -> FCompose (List.map g l)
    | Pre(l) -> Pre(g l)
    | _ -> e
  in
  recursion_transform recursion_direction f z
;;

let meta_transform_intexpr_on_intexpr (recursion_direction: recursion_direction) (f : intexpr -> intexpr) : (intexpr -> intexpr) = 
  let z (g : intexpr -> intexpr) (e : intexpr) : intexpr = 
    match e with
    | IMul (l) -> IMul(List.map g l)
    | IPlus (l) -> IPlus(List.map g l)
    | IDivPerfect(a,b) -> IDivPerfect(g a,g b)
    | _ -> e
  in
  recursion_transform recursion_direction f z
;;

let meta_transform_idxfunc_on_spl (recursion_direction: recursion_direction) (f : idxfunc -> idxfunc) : (spl -> spl) =
  let g = meta_transform_idxfunc_on_idxfunc recursion_direction f in
  meta_transform_spl_on_spl recursion_direction ( function 
  | G(l) -> G(g l) 
  | S(l) -> S(g l) 
  | Diag(l) -> Diag( g l)
  | x -> x)
;;

let meta_transform_intexpr_on_idxfunc (recursion_direction: recursion_direction) (f : intexpr -> intexpr) : (idxfunc -> idxfunc) =
  let g = meta_transform_intexpr_on_intexpr recursion_direction f in
  let rec z (e : idxfunc) : idxfunc = 
    match e with
    | FH (a, b, c, d) -> let ga = g a in
  			 let gb = g b in
  			 let gc = g c in
  			 FH (ga, gb, gc, g d)
    | FL (a, b) -> let ga = g a in FL (ga, g b)
    | FD (a, b) -> let ga = g a in FD (ga, g b)
    | FCompose a -> FCompose(List.map z a)
    | Pre a -> Pre(z a) 
    | PreWrap (n,f,funcs,d) -> PreWrap(n, f, funcs, (g d)) (*f is not parameterized because we don't want to parameterize inside the call*)
    | FArg (i,f) ->  FArg(i, (g f)) 
  in
  meta_transform_idxfunc_on_idxfunc recursion_direction z
;;

let meta_transform_intexpr_on_spl (recursion_direction: recursion_direction) (f : intexpr -> intexpr) : (spl -> spl) = 
  let g = meta_transform_intexpr_on_intexpr recursion_direction f in
  let intexprs_in_spl (e : spl) : spl = 
    match e with
      Compose _ | Tensor _ | RS _ | Diag _ | G _| S _ -> e
    | ISum(v,c,a) -> ISum(g v,g c,a)
    | L (n, m) -> L(g n, g m)
    | T (n, m) -> T(g n, g m)
    | I n -> I(g n)
    | DFT n -> DFT (g n)
    | BB _ -> e
    | UnpartitionnedCall _ -> e
    | PartitionnedCall _ -> e
    | F _ -> e
    | ISumReinitCompute _| Compute _ | ISumReinitConstruct _ | Construct _ -> assert false
  in
  fun (e : spl) ->
    (meta_transform_spl_on_spl recursion_direction intexprs_in_spl) ((meta_transform_idxfunc_on_spl recursion_direction (meta_transform_intexpr_on_idxfunc recursion_direction g)) e)
;;

let meta_collect_spl_on_spl (f : spl -> 'a list) : (spl -> 'a list) =
  let z (g : spl -> 'a list) (e : spl) : 'a list =
    match e with
      Compose l | Tensor l -> List.flatten (List.map g l)
    | ISum(_,_,a) -> g a
    | RS a -> g a
    | _ -> []
  in
  recursion_collect f z
;;

let meta_collect_idxfunc_on_idxfunc (f : idxfunc -> 'a list) : (idxfunc -> 'a list) =
  let z (g : idxfunc -> 'a list) (e : idxfunc) : 'a list =
    match e with
      FH _ | FL _ | FD _ -> []
    | FCompose l ->  List.flatten (List.map g l)
    | Pre x -> g x
    | PreWrap _ -> []
    | FArg _ -> []
  in
  recursion_collect f z
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

let meta_collect_boolexpr_on_boolexpr (f : boolexpr -> 'a list) : (boolexpr -> 'a list) =
  let z (g : boolexpr -> 'a list) (e : boolexpr) : 'a list =
    match e with
    | And (l) -> List.flatten (List.map g l)
    | Not(b) -> g b
    | _ -> []
  in
  recursion_collect f z
;;

let meta_collect_idxfunc_on_spl (f : idxfunc -> 'a list) : (spl -> 'a list) =
  meta_collect_spl_on_spl ( function
  | G(l) -> f l
  | S(l) -> f l
  | Diag(l) -> f l
  | _ -> []
  )
;;

let meta_collect_intexpr_on_idxfunc (f : intexpr -> 'a list) : (idxfunc -> 'a list) = 
  meta_collect_idxfunc_on_idxfunc ( function
  | FH (a, b, c, d) -> (f a) @ (f b) @ (f c) @ (f d)
  | FL(n, m) | FD(n,m) -> (f n) @ (f m)
  | _ -> []
  )
;;

let meta_collect_intexpr_on_boolexpr (f : intexpr -> 'a list) : (boolexpr -> 'a list) = 
  meta_collect_boolexpr_on_boolexpr ( function
  | IsPrime x -> f x
  | _ -> []
  )
;;

let meta_collect_intexpr_on_spl (f : intexpr -> 'a list) : (spl -> 'a list) =
  let direct_from_spl (ff : intexpr -> 'a list) (e : spl) : 'a list =
    match e with
      Compose _ | Tensor _ | RS _ | Diag _ | G _| S _ | UnpartitionnedCall _ | PartitionnedCall _ -> []
    | ISum(v,c,a) -> (ff v) @ (ff c)
    | L (n, m) -> (ff n) @ (ff m)
    | T (n, m) -> (ff n) @ (ff m)
    | I n -> ff n
    | DFT n -> ff n
    | ISumReinitCompute _| Compute _ | ISumReinitConstruct _ | Construct _ -> assert false
  in
  fun (e : spl) ->
    let ff = meta_collect_intexpr_on_intexpr f in
    ((meta_collect_spl_on_spl (direct_from_spl ff )) e)
    @ ((meta_collect_idxfunc_on_spl (meta_collect_intexpr_on_idxfunc ff)) e)
;;

let meta_iter_spl_on_spl (f : spl -> unit) : (spl -> unit) =
  fun (e : spl) ->
    ignore((meta_collect_spl_on_spl (fun (e:spl) -> f e;[])) e)
;;

let meta_iter_idxfunc_on_idxfunc (f : idxfunc -> unit) : (idxfunc -> unit) =
  fun (e : idxfunc) ->
    ignore((meta_collect_idxfunc_on_idxfunc (fun (e:idxfunc) -> f e;[])) e)
;;

let meta_iter_idxfunc_on_spl (f : idxfunc -> unit) : (spl -> unit) =
  fun (e : spl) ->
    ignore((meta_collect_idxfunc_on_spl (fun (e:idxfunc) -> f e;[])) e)
;;

let meta_iter_intexpr_on_intexpr (f : intexpr -> unit) : (intexpr -> unit) =
  fun (e : intexpr) ->
    ignore(meta_collect_intexpr_on_intexpr (fun (e:intexpr) -> f e;[]) e)
;;

let meta_iter_intexpr_on_boolexpr (f : intexpr -> unit) : (boolexpr -> unit) =
  fun (e : boolexpr) ->
    ignore(meta_collect_intexpr_on_boolexpr (fun (e:intexpr) -> f e;[]) e)
;;

let meta_iter_intexpr_on_idxfunc(f : intexpr -> unit) : (idxfunc -> unit) =
  fun (e : idxfunc) ->
    ignore(meta_collect_intexpr_on_idxfunc (fun (e:intexpr) -> f e;[]) e)
;;

let meta_iter_intexpr_on_spl(f : intexpr -> unit) : (spl -> unit) =
  fun (e : spl) ->
    ignore(meta_collect_intexpr_on_spl (fun (e:intexpr) -> f e;[]) e)
;;

let meta_compose_spl (recursion_direction: recursion_direction) (f : spl list -> spl list) : (spl -> spl) =
  meta_transform_spl_on_spl recursion_direction ( function 
  | Compose (l) -> Compose (f l) 
  | x -> x)
;;

let meta_tensorize_spl (recursion_direction: recursion_direction) (f : spl list -> spl list) : (spl -> spl) =
  meta_transform_spl_on_spl recursion_direction ( function 
  | Tensor (l) -> Tensor (f l) 
  | x -> x)
;;

let meta_multiply_intexpr (recursion_direction : recursion_direction) (f : intexpr list -> intexpr list) : (spl -> spl) =
  meta_transform_intexpr_on_spl recursion_direction ( function 
  | IMul (l) -> IMul (f l) 
  | x -> x)
;;

let meta_compose_idxfunc (recursion_direction : recursion_direction) (f : idxfunc list -> idxfunc list) : (spl -> spl) =
  meta_transform_idxfunc_on_spl recursion_direction ( function 
  | FCompose (l) -> FCompose (f l) 
  | x -> x)
;;

(*********************************************
	 RANGE AND DOMAIN                 
*********************************************)

let rec func_range (e : idxfunc) : intexpr = 
  match e with
  FH (_, range,_,_) -> range
| FL (n, _) -> n
| FD (n, _) -> n
| FCompose (l) -> func_range (List.hd l)
| Pre(l) -> func_range l
;;

let rec func_domain (e : idxfunc) : intexpr = 
  match e with
  FH (domain, _,_,_) -> domain
| FL (n, _) -> n
| FD (n, _) -> n
| FCompose (l) -> func_domain (List.hd (List.rev l))
| Pre(l) -> func_domain l
| PreWrap(_,_,_,d) -> d
| FArg (_,d)->d
;;

let rec range (e :spl) : intexpr = 
  match e with
    DFT(n) -> n
  | Tensor (list) -> IMul(List.map range list)
  | I(n) -> n
  | T(n, _) -> n
  | L(n, _) -> n
  | Compose ( list ) -> range (List.hd list)
  | S (f) -> func_range f
  | G (f) -> func_domain f
  | Diag (f) -> func_domain f
  | ISum (_, _, spl) -> range spl
  | RS (spl) -> range spl
  | F(n) -> IConstant n
  | BB(spl) -> range spl
  | UnpartitionnedCall _ -> assert false
  | PartitionnedCall _ -> assert false
  | ISumReinitCompute (_, _, _, _, _, range, _) -> range
  | Compute (_,_,_,range,_) -> range
  | ISumReinitConstruct _ -> assert false
  | Construct _ -> assert false
;;    

let rec domain (e :spl) : intexpr = 
  match e with
    DFT(n) -> n
  | F(n) -> IConstant n
  | Tensor (list) -> IMul(List.map range list)
  | I(n) -> n
  | T(n, _) -> n
  | L(n, _) -> n
  | Compose ( list ) -> domain (List.hd (List.rev list))
  | S (f) -> func_domain f
  | G (f) -> func_range f
  | Diag (f) -> func_domain f (* by definition a diag range is equal to a diag domain. However the range of the function is larger but noone cares since its precomputed*)
  | ISum (_, _, spl) -> domain spl
  | RS (spl) -> domain spl
  | BB(spl) -> domain spl
  | UnpartitionnedCall _ -> assert false
  | PartitionnedCall _ -> assert false
  | ISumReinitCompute (_, _, _, _, _, _, domain) -> domain
  | Compute (_,_,_,_,domain) -> domain
  | ISumReinitConstruct _ -> assert false
  | Construct _ -> assert false
;;    

(*********************************************
	 RULES                 
*********************************************)

let rule_remove_unary_fmul : (spl -> spl) =
  meta_transform_intexpr_on_spl BottomUp ( function 
  | IMul ([x]) -> x
  | x -> x)
;;

let rule_multiply_by_one : (spl -> spl) =
  let rec f (l : intexpr list) : intexpr list = 
  match l with
  | IConstant 1 :: tl -> f tl
  | a :: tl -> a :: (f tl)
  | [] -> []
  in
  meta_multiply_intexpr BottomUp f
;;

let rule_multiply_and_divide_by_the_same : (spl -> spl) =
  let rec f (l : intexpr list) : intexpr list = 
  match l with
  | a :: IDivPerfect(b, c) :: tl  when a = c -> f (b::tl)
  | IDivPerfect(a, b) :: c :: tl  when b = c -> f (a::tl)
  | a :: tl -> a :: (f tl)
  | [] -> []
  in
  meta_multiply_intexpr BottomUp f
;;

let gen_loop_counter =
object 
  val tbl = ref 0;
  method get () : intexpr = 
    tbl := !tbl + 1;
    ILoopCounter !tbl
end
;;

let rule_tensor_to_isum : (spl -> spl) =
  let rec f (l : spl list) : spl list = 
    match l with
      I(k) :: a :: tl ->
	let i = gen_loop_counter#get () in 
	f ( ISum(i, k, Compose( [S(FH(range a, IMul([range a; k]), IMul([range a; i]), IConstant 1)); a ; G(FH(domain a, IMul([domain a; k]), IMul([domain a; i]), IConstant 1)) ] )) :: tl)
    | a :: I(k) :: tl -> 
      let i = gen_loop_counter#get () in 
      f ( ISum(i, k, Compose( [S(FH(range a, IMul([range a; k]), i, k)); a; G(FH(domain a, IMul([domain a; k]), i, k)) ] )) :: tl)
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_tensorize_spl BottomUp f
;;

(* YSV thesis 2.44 *)
let rule_suck_inside_isum : (spl -> spl) =
  let rec f (l : spl list) : spl list = 
  match l with
    ISum(v, c, a)::L(n,k)::tl -> f (ISum(v, c, Compose([a ; G(FL(n,k))])) :: tl) 
  | ISum(v, c, a)::(Diag _ as d)::tl -> f (ISum(v, c, Compose([a ; d ])) :: tl)
  | ISum(v, c, a)::G(h)::tl -> f (ISum(v, c, Compose([a ; G(h) ])) :: tl) 
  | S(h)::ISum(v, c, a)::tl -> f (ISum(v, c, Compose([S(h); a ])) :: tl) 
  | a::tl -> a :: (f tl)
  | [] -> []
  in
  meta_compose_spl BottomUp f
;;

let rule_transorm_T_into_diag : (spl -> spl) =
  meta_transform_spl_on_spl BottomUp (function 
  | T(n,k) -> Diag(Pre(FD(n,k)))
  | x -> x
  )
;;

let rule_suck_inside_RS : (spl -> spl) =
  let rec f (l : spl list) : spl list = 
  match l with
    RS(a)::b::tl -> f (RS(Compose([a;b])) :: tl)
  | a::RS(b)::tl -> f (RS(Compose([a;b])) :: tl)
  | a::tl -> a :: (f tl)
  | [] -> []
  in
  meta_compose_spl BottomUp f
;;

let rule_remove_unary_compose : (spl -> spl) =
  meta_transform_spl_on_spl BottomUp ( function
  |Compose ([a]) -> a
  | x -> x)
;;

let rule_remove_unary_tensor : (spl -> spl) =
  meta_transform_spl_on_spl BottomUp ( function
  |Tensor ([a]) -> a
  | x -> x)
;;

let rule_flatten_compose : (spl -> spl) =
  let rec f (l : spl list) : spl list = 
  match l with
  | Compose(a)::tl -> f (a @ tl)
  | a::tl -> a :: (f tl)
  | [] -> []
  in
  meta_compose_spl BottomUp f
;;  

let rule_flatten_fcompose : (spl -> spl) =
  let rec f (l : idxfunc list) : idxfunc list = 
  match l with
    FCompose(a)::tl -> f (a @ tl)
  | a::tl -> a :: (f tl)
  | [] -> []
  in
  meta_compose_idxfunc BottomUp f
;;  

let rule_remove_unary_fcompose : (spl -> spl) =
  meta_transform_idxfunc_on_spl BottomUp ( function
  |FCompose ([a]) -> a
  | x -> x)
;;

let rule_compose_gather_gather : (spl -> spl) =
  let rec f (l : spl list) : spl list =
  match l with
    G(a)::G(b)::tl -> f (G(FCompose [b;a]) :: tl)
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_compose_spl BottomUp f
;;

let rule_compose_scatter_scatter : (spl -> spl) =
  let rec f (l : spl list) : spl list =
  match l with
    S(a)::S(b)::tl -> f (S(FCompose [a;b]) :: tl)
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_compose_spl BottomUp f
;;

let rule_compose_gather_diag : (spl -> spl) =
  let rec f (l : spl list) : spl list =
    match l with
      G(a)::Diag(b)::tl -> f (Diag(FCompose [b;a]) :: G(a) :: tl)
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_compose_spl BottomUp f
;;

let rule_compose_BB_diag : (spl -> spl) =
  let rec f (l : spl list) : spl list =
    match l with
      BB(spl)::Diag(b)::tl -> BB(Compose([spl;Diag(b)]))::tl
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_compose_spl BottomUp f
;;

let rule_compose_BB_gather : (spl -> spl) =
  let rec f (l : spl list) : spl list =
    match l with
      BB(spl)::G(b)::tl -> BB(Compose([spl;G(b)]))::tl
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_compose_spl BottomUp f
;;

let rule_compose_scatter_BB : (spl -> spl) =
  let rec f (l : spl list) : spl list =
    match l with
      S(b)::BB(spl)::tl -> BB(Compose([S(b);spl]))::tl
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_compose_spl BottomUp f
;;

    
let rule_compose_FL_FH : (spl -> spl) =
  let rec f (l : idxfunc list) : idxfunc list =
  match l with
    FL(n1,k) :: FH(m1,n2,IMul(m2::multl), IConstant 1) :: tl when m1 = m2 -> f (FH(m1, n2, IMul(multl), k) :: tl) 
    (*n1 = n2 is not checked because n could be mul(k,m) *)
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_compose_idxfunc BottomUp f
;;

let rule_compose_FH_FH : (spl -> spl) =
  let rec f (l : idxfunc list) : idxfunc list =
  match l with
    FH(gn1,gnp,bp,sp) :: FH(n,gn2,b,s) :: tl -> f (FH(n, gnp, IPlus([bp;IMul([sp; b])]), IMul([sp; s])) :: tl)
    (*gn1 = gn2 is not checked because that could be non-obvious*)
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_compose_idxfunc BottomUp f
;;

let rule_compose_FHH_FHH : (spl -> spl) =
  let rec f (l : idxfunc list) : idxfunc list =
    match l with
    | FHH(da,ra,ba,sa, vsa) :: FHH(db, rb, bb, sb, vsb) :: tl ->
       let rec mul (a:intexpr list) (b:intexpr list) : intexpr list =
	 match a,b with
	 |[], [] -> []
	 |[], (y::ys) -> IMul([sa;y])::(mul [] ys) 
	 |x, [] -> x
	 |(x::xs),(y::ys) -> IPlus([x;IMul([sa;y])])::(mul xs ys)
       in
       f (FHH(db,ra, IPlus([ba;IMul([sa; bb])]), IMul([sa; sb]), (mul vsa vsb)) :: tl)
    (*rb = da is not checked because that could be non-obvious*)
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_compose_idxfunc BottomUp f
;;

let rule_distribute_uprank : (spl -> spl) =
  meta_transform_idxfunc_on_spl TopDown ( function
  | FUp (FCompose list) -> FCompose( List.map (fun x-> FUp(x)) list)
  | x -> x)
;;

let rule_distribute_downrank : (spl -> spl) =
  meta_transform_idxfunc_on_spl TopDown ( function
  | FDown (FCompose list, j, l) -> FCompose( List.map (fun x-> FDown(x, j, l)) list)
  | x -> x)
;;

let rule_uprank_FHH : (spl -> spl) =
  meta_transform_idxfunc_on_spl TopDown ( function
  | FUp (FHH(d,r,b,s,vs)) -> FHH(d,r,b,s,(IConstant 0::vs))
  | x -> x)
;;

let rule_downrank_FHH : (spl -> spl) =
  let rec extract (l:int) (vs:intexpr list) : intexpr * intexpr list =
    let (x::xs)=vs in
    if (l=0) then
      (x, xs)
    else
      let (a,b) = extract (l-1) xs in
      (a,x::b)
  in
  meta_transform_idxfunc_on_spl TopDown ( function
  | FDown (FHH(d,r,b,s,vs), j , l) ->
     let(content,remainder)= extract l vs in
     FHH(d,r, IPlus([b;IMul([content;j])]), s, remainder)
  | x -> x)
;;


let rule_suck_inside_pre : (spl -> spl) = 
  let rec f (l : idxfunc list) : idxfunc list =
  match l with
    Pre(a)::b::tl -> f (Pre(FCompose([a;b])) :: tl)
  | a::tl -> a :: (f tl)
  | [] -> []
  in
  meta_compose_idxfunc BottomUp f  
;;

let rec apply_rewriting_rules (e : spl) : spl = 
  let add_pair (map) (name, rule) =
    StringMap.add name rule map
  in
  let rules = 
    List.fold_left add_pair StringMap.empty [
      ("Tensor to ISum", rule_tensor_to_isum);
      ("Remove unary tensor", rule_remove_unary_tensor);
      ("Remove unary compose", rule_remove_unary_compose); 
      ("Remove unary fcompose", rule_remove_unary_fcompose);
      ("Transform T into diag", rule_transorm_T_into_diag);
      ("Rule suck inside pre", rule_suck_inside_pre);
      ("Remove unary fmul", rule_remove_unary_fmul);
      ("Suck inside ISum", rule_suck_inside_isum);
      ("Suck inside RS", rule_suck_inside_RS);
      ("Flatten Compose", rule_flatten_compose);
      ("Flatten FCompose", rule_flatten_fcompose);
      ("Compose Gather Gather", rule_compose_gather_gather);
      ("Compose Scatter Scatter", rule_compose_scatter_scatter);
      ("Compose_l_h", rule_compose_FL_FH);
      ("Compose_h_h", rule_compose_FH_FH);
      ("Compose Gather Diag", rule_compose_gather_diag);
      ("Compose BB Diag", rule_compose_BB_diag);
      ("Compose BB Gather", rule_compose_BB_gather);
      ("Compose Scatter BB", rule_compose_scatter_BB);
      ("Multiply by one", rule_multiply_by_one);
      ("Multiply and divide by the same", rule_multiply_and_divide_by_the_same);
      ("Distribute uprank", rule_distribute_uprank);
      ("Distribute downrank", rule_distribute_downrank);
      ("Downrank FHH", rule_downrank_FHH);
      ("Uprank FHH", rule_uprank_FHH);
      ("FCompose FHH with FHH", rule_compose_FHH_FHH);
    ]
  in
  let apply_rewriting_rules_once (e : spl) : spl = 
    let f (name:string) (rule : spl -> spl) (e : spl) : spl=
      let res = rule e
      in
(*      if (e <> outcome) then print_endline ("===  " ^ name ^ "  ===\n    " ^ (string_of_spl e) ^ "\n    " ^ (string_of_spl outcome) ^ "\n") ;  *)
      res
    in
    StringMap.fold f rules e
  in
  let next = apply_rewriting_rules_once e in
  if (e = next) then e else (apply_rewriting_rules next)
;;

