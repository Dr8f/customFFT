let optional_short_print (w : string) (s : string) : string = 
  let short_print = true
  in
  if (short_print) then
    s
  else
    w ^ "(" ^ s ^ ")"
;;


module StringMap = Map.Make(String)
;;

module IntMap = Map.Make(struct type t = int let compare = compare end)
;;

exception InvalidDimException
;;

type intvar = 
| IFreedom of int
| ILoopCounter of int
| IArg of int
| ITranscendental of string
;;

type intexpr =
  IConstant of int
| IVar of intvar
| IMul of intexpr list
| IPlus of intexpr list
| IDivPerfect of intexpr * intexpr 
| IDivisor of intexpr
| IWrap of int * intexpr
;;

type boolexpr =
  IsNotPrime of intexpr
| And of boolexpr list
| IntEqual of intexpr * intexpr
;;

let gen_freedom_var =
object 
  val tbl = ref 0;
  method get () : intexpr = 
    tbl := !tbl + 1;
    IVar (IFreedom !tbl)
end
;;

let gen_loop_counter =
object 
  val tbl = ref 0;
  method get () : intexpr = 
    tbl := !tbl + 1;
    IVar (ILoopCounter !tbl)
end
;;


type idxfunc = 
  FH of intexpr * intexpr * intexpr * intexpr
| FL of intexpr * intexpr
| FD of intexpr * intexpr
| FCompose of idxfunc list
| Pre of idxfunc
;;

type recursion_direction = 
  BottomUp 
| TopDown
;;

type spl =
DFT of intexpr
| RS of spl
| Tensor of spl list
| I of intexpr
| T of intexpr * intexpr
| L of intexpr * intexpr
| Compose of spl list
| S of idxfunc
| G of idxfunc
| Diag of idxfunc
| ISum of intexpr * intexpr * spl
| Call of string * intexpr IntMap.t
| ActualCall of string * intexpr list * intexpr list * intexpr list 
;;

let string_of_intvar (e : intvar) : string =
  match e with
  | IFreedom i -> "f"^(string_of_int i)
  | ILoopCounter i -> "i" ^ (string_of_int i)
  | IArg i -> "u"^(string_of_int i)
  | ITranscendental s -> s
;; 

let rec string_of_intexpr (e : intexpr) : string =
  match e with
    IConstant i -> string_of_int i
  | IMul (l) -> optional_short_print "IMul" (String.concat " * " (List.map string_of_intexpr l))
  | IPlus (l) -> optional_short_print "IPlus" (String.concat " + " (List.map string_of_intexpr l))
  | IDivPerfect(l,r) -> optional_short_print "IDivPerfect" ((string_of_intexpr l)^"/"^(string_of_intexpr r))
  | IWrap (l,r) -> "["^string_of_int l^"]"^string_of_intexpr r
  | IDivisor(l)->"divisor("^string_of_intexpr l^")"
  | IVar(s) -> string_of_intvar s
;;

let rec string_of_boolexpr (e : boolexpr) : string = 
  match e with
    IsNotPrime(l)->"isNotPrime("^string_of_intexpr l^")"
  | And(l)->optional_short_print "And" (String.concat " && " (List.map string_of_boolexpr l))
  | IntEqual(l,r)->"("^(string_of_intexpr l)^" == "^(string_of_intexpr r)^")"
;;

let string_of_intexpr_intexpr ((e,f) : intexpr * intexpr) : string = 
  (string_of_intexpr e)^"="^(string_of_intexpr f)
;;

let string_of_int_intexpr ((e,f):int * intexpr) : string =
  "["^(string_of_int e)^"]"^(string_of_intexpr f)
;;


let rec string_of_idxfunc (e : idxfunc) : string =
  match e with
    FH(src, dest, j,k) -> "h("^(string_of_intexpr src)^","^(string_of_intexpr dest)^","^(string_of_intexpr j)^","^(string_of_intexpr k)^")"
  | FL(j,k) -> "l("^(string_of_intexpr j)^","^(string_of_intexpr k)^")"      
  | FD(j,k) -> "d("^(string_of_intexpr j)^","^(string_of_intexpr k)^")"      
  | FCompose(list) -> optional_short_print "fCompose" (String.concat " . " (List.map string_of_idxfunc list))
  | Pre(l) -> "pre("^(string_of_idxfunc l)^")"
;;

let rec string_of_spl (e : spl) : string =
  match e with
    DFT (n) -> "DFT("^(string_of_intexpr n)^")"
  | Tensor (list) ->  String.concat " x " (List.map string_of_spl list)
  | I (n) -> "I("^(string_of_intexpr n)^")"
  | T (n, m) -> "T("^(string_of_intexpr n)^","^(string_of_intexpr m)^")"
  | L (n, m) -> "L("^(string_of_intexpr n)^","^(string_of_intexpr m)^")"
  | Compose (list) -> optional_short_print "Compose" (String.concat " . " (List.map string_of_spl list))
  | S (f) -> "S("^(string_of_idxfunc f)^")"
  | G (f) -> "G("^(string_of_idxfunc f)^")"
  | Diag (f) -> "Diag("^(string_of_idxfunc f)^")"
  | ISum (i, high, spl) -> "ISum("^(string_of_intexpr i)^","^(string_of_intexpr high)^","^(string_of_spl spl)^")"
  | RS(spl) -> "RS("^(string_of_spl spl)^")"
  | Call(f, l) -> 
    f^"("^(String.concat "," (List.map string_of_int_intexpr (IntMap.bindings l)))^")"
  | ActualCall(f, cold, reinit, hot) -> 
    f^"("^(String.concat "," (List.map string_of_intexpr cold)) ^ ")"^"("^(String.concat "," (List.map string_of_intexpr reinit)) ^ ")"^"("^(String.concat "," (List.map string_of_intexpr hot)) ^ ")"
;;

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
  | Call _ -> raise InvalidDimException
  | ActualCall _ -> raise InvalidDimException
;;    

let rec domain (e :spl) : intexpr = 
  match e with
    DFT(n) -> n
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
  | Call _ -> raise InvalidDimException
  | ActualCall _ -> raise InvalidDimException
;;    

(*********************************************
	 METARULES                 
*********************************************)

let recursion_transform (recursion_direction: recursion_direction) (f : 'a -> 'a) (z : ('a -> 'a) -> 'a -> 'a) : ('a -> 'a) =
  let rec g (e : 'a) : 'a =
    match recursion_direction with
      BottomUp -> f (z g e)
    | TopDown -> z g (f e)
  in
  g  
;;

let meta_transform_spl_on_spl (recursion_direction: recursion_direction) (f : spl -> spl) : (spl -> spl) =
  let z (g : spl -> spl) (e : spl) : spl = 
    match e with
    | Compose (l) -> Compose (List.map g l)
    | Tensor (l) -> Tensor (List.map g l)
    | ISum(v,c,a) -> ISum(v,c, (g a))
    | RS (l) -> RS(g l)
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
    | Call _ -> e
    | ActualCall _ -> e
  in
  let intexprs_in_idxfunc (e : idxfunc) : idxfunc =
    match e with 
      FH (a, b, c, d) -> let ga = g a in 
			 let gb = g b in
			 let gc = g c in
			 FH (ga, gb, gc, g d)
    | FL (a, b) -> let ga = g a in FL (ga, g b)
    | FD (a, b) -> let ga = g a in FD (ga, g b)
    | FCompose _ -> e
    | Pre _ -> e
  in
  fun (e : spl) ->
    (meta_transform_spl_on_spl recursion_direction intexprs_in_spl) ((meta_transform_idxfunc_on_spl recursion_direction intexprs_in_idxfunc) e)
;;



let recursion_collect (f : 'a -> 'b list) (z : ('a -> 'b list) -> 'a -> 'b list) : ('a -> 'b list) =
  let rec g (e : 'a) : 'b list =
    f e @ (z g e)
  in
  g
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
  | IsNotPrime x -> f x
  | _ -> []
  )
;;

let meta_collect_intexpr_on_spl (f : intexpr -> 'a list) : (spl -> 'a list) =
  let direct_from_spl (ff : intexpr -> 'a list) (e : spl) : 'a list =
    match e with
      Compose _ | Tensor _ | RS _ | Diag _ | G _| S _ | Call _ | ActualCall _ -> []
    | ISum(v,c,a) -> (ff v) @ (ff c)
    | L (n, m) -> (ff n) @ (ff m)
    | T (n, m) -> (ff n) @ (ff m)
    | I n -> ff n
    | DFT n -> ff n
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


let rule_tensor_to_isum : (spl -> spl) =
  let rec f (l : spl list) : spl list = 
    match l with
      I(k) :: a :: tl ->
	let i = gen_loop_counter#get () in 
	f ( ISum(i, k, Compose( [S(FH(range a, IMul([range a; k]), IMul([range a; i]), IConstant 1)); a ; G(FH(domain a, IMul([domain a; k]), IMul([domain a; i]), IConstant 1)) ] )) :: tl)
    | a :: I(k) :: tl -> 
      let i = gen_loop_counter#get () in 
      f ( ISum(i, k, Compose( [S(FH(range a, IMul([range a; k]), i, k)); a; G(FH(domain a, IMul([domain a; k]),i , k)) ] )) :: tl)
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
    Compose(a)::tl -> f (a @ tl)
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


let rule_suck_inside_pre : (spl -> spl) = 
  let rec f (l : idxfunc list) : idxfunc list =
  match l with
    Pre(a)::b::tl -> f (Pre(FCompose([a;b])) :: tl)
  | a::tl -> a :: (f tl)
  | [] -> []
  in
  meta_compose_idxfunc BottomUp f  
;;



let rules = 
  let add_pair (map) (name,rule) =
    StringMap.add name rule map
  in
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
    ("Multiply by one", rule_multiply_by_one);
    ("Multiply and divide by the same", rule_multiply_and_divide_by_the_same);
  ]
;;

let rec apply_rewriting_rules (e : spl) : spl = 
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

(**********************
      ALGO
***********************)

let algo_cooley_tukey : spl -> boolexpr * (intexpr*intexpr) list * spl =
  function (e:spl) ->
    let conditions = ref [] in
    let freedoms = ref [] in 
    let f = meta_transform_spl_on_spl BottomUp ( function
      |DFT n -> 	    
	conditions := IsNotPrime(n) :: !conditions;
	let k = gen_freedom_var#get () in
	freedoms := (k, IDivisor n) :: !freedoms;
	let m = IDivPerfect(n, k) in
	Compose([Tensor( [DFT(k); I(m)]); T(n, m); Tensor([I(k); DFT(m)]); L(n,k)])
      | x -> x) in
    ((And !conditions), !freedoms, f e)
;;  

(**********************
      CLOSURE
***********************)

let mark_RS : spl -> spl =
  meta_transform_spl_on_spl BottomUp ( function
  |DFT n -> RS(DFT(n))
  | x -> x)
;;  

let collect_RS: spl -> spl list =
  meta_collect_spl_on_spl ( function
  | RS(x) -> [x]
  | _ -> []
)
;;

let rec extract_constraints_func (e : idxfunc) : (intexpr * intexpr) list =
  let rec extract_constraints_within_fcompose (e : idxfunc list) (res : (intexpr * intexpr) list) : (intexpr * intexpr) list = 
    match e with
      x :: (y :: tl as etl) -> let dmn = func_domain x in
			       let rng = func_range y in
			       (* print_string ("!!!!"^(string_of_intexpr dmn)^"="^(string_of_intexpr rng)^"\n") ;   *)
			       extract_constraints_within_fcompose etl ((dmn, rng) :: res)
    | [x] -> res;
    | [] -> res
  in
  match e with
  | FCompose l -> extract_constraints_within_fcompose l (List.flatten (List.map extract_constraints_func l))
  | Pre x -> extract_constraints_func x 
  | _ -> []
;;


let rec extract_constraints_spl (e : spl) : (intexpr * intexpr) list =
  let rec extract_constraints_within_compose (e : spl list) ( res : (intexpr * intexpr) list) : (intexpr * intexpr) list = 
    match e with
      x :: (y :: tl as etl) -> let dmn = domain x in
			       let rng = range y in
			       (* print_string ((string_of_intexpr dmn)^"="^(string_of_intexpr rng)^"\n") ;  *)
			       extract_constraints_within_compose etl ((dmn, rng) :: res)
    | [x] -> res;
    | [] -> res
  in
  match e with 
    Compose l -> extract_constraints_within_compose l (List.flatten (List.map extract_constraints_spl l))
  | Diag x -> extract_constraints_func x
  | _ -> []    
;;

let rec reconcile_constraints (constraints : (intexpr * intexpr) list) (spl : spl) : spl =
  match constraints with
    (l,r) :: tl -> let f (e : intexpr) : intexpr = if (e=r) then l else e in
		   reconcile_constraints (List.map (fun (l,r) -> (f l, f r)) tl) ((meta_transform_intexpr_on_spl TopDown f) spl)
  | [] -> spl
;;

let wrap_intexprs_naively (e :spl) : spl =
  let count = ref 0 in
  let f (i : intexpr) : intexpr = 
    match i with 
      IMul _ | IPlus _ | IDivPerfect _ | IVar _ -> 
	count := !count + 1;
	IWrap(!count, i)
    | x -> x
  in
  (meta_transform_intexpr_on_spl TopDown f) e
;;

let wrap_intexprs (e : spl) : spl  =
  let wrapup = wrap_intexprs_naively e in
  let constraints = extract_constraints_spl wrapup in
  let res = reconcile_constraints constraints wrapup in
  res
;;

let reintegrate_RS (e: spl) (canonized : spl list) : spl =
  let rem = ref canonized in
  let f (e:spl) : spl =
    match e with
    | RS _ -> let hd = List.hd !rem in 
	      rem := List.tl !rem;
	      RS (hd)
    | x -> x
  in
  (meta_transform_spl_on_spl TopDown f) e
;;

let unwrap (e:spl) : spl =
  let g (e:intexpr) : intexpr = 
    match e with
      IWrap(l,r)->IVar(IArg l)
    | x -> x
  in
  (meta_transform_intexpr_on_spl TopDown g) e
;;

module SplMap = Map.Make (struct
  type t = spl
  let compare = Pervasives.compare
end)


let drop_RS : (spl -> spl) =
  let g (e : spl) : spl = 
    match e with
    | RS(x) -> x
    | x -> x
  in
  meta_transform_spl_on_spl BottomUp g
;;

let replace_by_a_call ((spl,name):spl * string) : spl =
  let collect_binds (spl:spl) : 'a list = 
    let binds (i : intexpr) : 'a list =
      match i with
	IWrap _ -> [i]
      | _ -> []
    in
    ((meta_collect_intexpr_on_spl binds) spl) in
  let rec mapify (binds : intexpr list) (map : 'a IntMap.t) : 'a IntMap.t =
    match binds with
      [] -> map
    | IWrap(p,expr)::tl -> mapify tl (IntMap.add p expr map)
    | _ -> failwith "type is not supported"
  in
  Call(name, (mapify (collect_binds spl) IntMap.empty ))
;;

module IntExprSet = Set.Make (struct
  type t = intexpr
  let compare = Pervasives.compare
end)
;;

type breakdown = (boolexpr * (intexpr * intexpr) list * spl* spl)
;;

type rstep_unpartitioned = (string * spl * IntExprSet.t * breakdown list )
;;

type rstep_partitioned = (string * spl * IntExprSet.t * IntExprSet.t * IntExprSet.t * breakdown list)
;;

let collect_args (rstep : spl) : IntExprSet.t = 
  let args = ref  IntExprSet.empty in
  let g (e : intexpr) : _ =
    match e with
    | IVar(IArg _) -> args := IntExprSet.add e !args
    | _ -> ()
  in
  meta_iter_intexpr_on_spl g rstep;
  !args
;;


let compute_the_closure (stems : spl list) (algo : spl -> boolexpr * (intexpr*intexpr) list * spl) : rstep_unpartitioned list = 
  let under_consideration = ref [] in
  let rsteps = ref [] in
  let namemap = ref SplMap.empty in
  let count = ref 0 in
  let register_name (rstep:spl) : _ =
    count := !count + 1;
    let name = "RS"^(string_of_int !count) in
    namemap := SplMap.add rstep name !namemap;
    under_consideration := !under_consideration@[rstep];    
  in
  let ensure_name (rstep:spl) : string =
    if not(SplMap.mem rstep !namemap) then (
      register_name rstep;
    );
    SplMap.find rstep !namemap
  in
  List.iter register_name stems;
  while (List.length !under_consideration != 0) do
    let rstep = List.hd !under_consideration in
    under_consideration := List.tl !under_consideration;
    let name = ensure_name rstep in
    let args = collect_args rstep in
    let (condition, freedoms, naive_desc) = algo rstep in
    let desc = apply_rewriting_rules (mark_RS(naive_desc)) in
    let wrapped_RSes = List.map wrap_intexprs (collect_RS desc) in
    let new_steps = List.map unwrap wrapped_RSes in
    let new_names = List.map ensure_name new_steps in
    let extracts_with_calls = List.map replace_by_a_call (List.combine wrapped_RSes new_names) in
    let desc_with_calls = drop_RS (reintegrate_RS desc extracts_with_calls) in
    rsteps := !rsteps @ [(name, rstep, args, [(condition, freedoms, desc, desc_with_calls)])];
  done;
  !rsteps
;;

let closure = compute_the_closure [DFT(IVar(IArg(1)))] algo_cooley_tukey
;;


type specified_arg = string * int
;;

module SpecArgMap = Map.Make (struct
  type t = specified_arg
  let compare = Pervasives.compare
end)
;;

module SpecArgSet = Set.Make (struct
  type t = specified_arg
  let compare = Pervasives.compare
end)
;;

let compute_dependency_map (closure: rstep_unpartitioned list) : SpecArgSet.t SpecArgMap.t =
  let depmap = ref SpecArgMap.empty in 
  let per_rstep ((name, _, _, breakdowns) : rstep_unpartitioned) : _=   
    let per_rule ((_,_,_,desc_with_calls):breakdown) : _ = 
      meta_iter_spl_on_spl ( function
      | Call(callee,vars) ->
	let g (arg:int) (expr:intexpr) : _ =
    	  let key = (callee,arg) in
    	  let h (e:intexpr): _ =
    	    match e with
    	      IVar (IArg i) ->
    		let new_content = (name,i) in
    		depmap :=
    		  if (SpecArgMap.mem key !depmap) then
    		    SpecArgMap.add key (SpecArgSet.add new_content (SpecArgMap.find key !depmap)) !depmap
    		  else
    		    SpecArgMap.add key (SpecArgSet.singleton new_content) !depmap
    	    | _ -> ()
    	  in
    	  meta_iter_intexpr_on_intexpr h expr
	in
	IntMap.iter g vars
      | _ -> ()
      ) desc_with_calls	
    in
    List.iter per_rule breakdowns
  in
  List.iter per_rstep closure;
  (!depmap)
;;

let compute_initial_hots (closure: rstep_unpartitioned list) : SpecArgSet.t =
  let hot_set = ref SpecArgSet.empty in
  let per_rstep ((name, _, _, breakdowns) : rstep_unpartitioned) : _=   
    let per_rule ((_,_,_,desc_with_calls):breakdown) : _ = 
      meta_iter_spl_on_spl ( function
      | Call(callee,vars) ->
	let g (arg:int) (expr:intexpr) : _ =
    	  let h (e:intexpr): _ =
    	    match e with
    	    | IVar (ILoopCounter _) -> hot_set := SpecArgSet.add (callee,arg) !hot_set 
    	    | _ -> ()
    	  in
    	  meta_iter_intexpr_on_intexpr h expr
	in
	IntMap.iter g vars
      | _ -> ()
      ) desc_with_calls	
    in
    List.iter per_rule breakdowns
  in
  List.iter per_rstep closure;
  !hot_set
;;



let compute_initial_colds (closure: rstep_unpartitioned list) : SpecArgSet.t =
  let cold_set = ref SpecArgSet.empty in

  let init_rstep ((name, rstep, args, breakdowns) : rstep_unpartitioned) : _=
    let add_args_to_cold (e:intexpr) : _ =
      match e with
	IVar (IArg i) -> 
	  cold_set := SpecArgSet.add (name,i) !cold_set
      | x -> ()
    in
    (* all arguments in the pre() marker must be cold *)
    let add_all_pre_to_cold (e:idxfunc) : _ =
      match e with 
      | Pre x -> 
	meta_iter_intexpr_on_idxfunc add_args_to_cold x
      | _ -> ()
    in
    meta_iter_idxfunc_on_spl add_all_pre_to_cold rstep;
    
    let init_rule ((condition,freedoms,desc,desc_with_calls):breakdown) : _ = 
      (* all arguments in condition (intexpr list) *)
      meta_iter_intexpr_on_boolexpr add_args_to_cold condition;
      
      (* all arguments in freedoms ((intexpr*intexpr) list) must be cold *)
      List.iter (meta_iter_intexpr_on_intexpr add_args_to_cold) (List.map snd freedoms)
    in
    List.iter init_rule breakdowns
  in
  List.iter init_rstep closure;
  !cold_set
;;


let backward_propagation (init_set:SpecArgSet.t) (dependency_map:SpecArgSet.t SpecArgMap.t) : SpecArgSet.t =
  let res = ref init_set in
  let dirty = ref true in
  let f (callee:specified_arg) (caller_set:SpecArgSet.t) : _ = 
    if SpecArgSet.mem callee !res then
      (
	let g (caller:specified_arg) : _= 
	  if not(SpecArgSet.mem caller !res) then
	  (
	    res := SpecArgSet.add caller !res;
	    dirty := true;
	  )	    
	in
	SpecArgSet.iter g caller_set;
      )
  in
  while (!dirty) do 
    dirty := false;
    SpecArgMap.iter f dependency_map;
  done ;
  !res
;;

let forward_propagation (init_set:SpecArgSet.t) (dependency_map:SpecArgSet.t SpecArgMap.t) : SpecArgSet.t =
  let res = ref init_set in
  let dirty = ref true in
  let forward_hot_propagation (callee:specified_arg) (caller_set:SpecArgSet.t) : _ = 
    if not(SpecArgSet.mem callee !res) then
      (
	let g (caller:specified_arg) : _= 
	  if SpecArgSet.mem caller !res then
	  (
	    res := SpecArgSet.add callee !res;
	    dirty := true;
	  )	    
	in
	SpecArgSet.iter g caller_set;
      )
  in
  while (!dirty) do 
    dirty := false;
    SpecArgMap.iter forward_hot_propagation dependency_map;
  done ;
  !res
;;

let filter_by_rstep (name:string) (s:SpecArgSet.t) : IntExprSet.t =
  let res = ref IntExprSet.empty in
  let f ((rs,i):specified_arg) : _ =
    if (rs = name) then
      res := IntExprSet.add (IVar(IArg i)) !res
  in
  SpecArgSet.iter f s;
  !res
;;

let compute_partition_map (closure: rstep_unpartitioned list) : (IntExprSet.t StringMap.t * IntExprSet.t StringMap.t * IntExprSet.t StringMap.t) = 
  let dependency_map = compute_dependency_map closure in
  let initial_all_colds = compute_initial_colds closure in
  let initial_all_hots = compute_initial_hots closure in
  let all_colds = backward_propagation initial_all_colds dependency_map in
  let all_hots = forward_propagation initial_all_hots dependency_map in

  let resC = ref StringMap.empty in
  let resR = ref StringMap.empty in
  let resH = ref StringMap.empty in
  let partition_args ((name, rstep, args, breakdowns) : rstep_unpartitioned) : _=
    let my_necessarily_colds = filter_by_rstep name all_colds in
    let my_necessarily_hots = filter_by_rstep name all_hots in
    let not_constrained = IntExprSet.diff args (IntExprSet.union my_necessarily_colds my_necessarily_hots) in
    let reinit = IntExprSet.inter my_necessarily_colds my_necessarily_hots in
    resR := StringMap.add name reinit !resR;
    resC := StringMap.add name (IntExprSet.diff my_necessarily_colds reinit) !resC;
    resH := StringMap.add name (IntExprSet.diff (IntExprSet.union my_necessarily_hots not_constrained) reinit) !resH (* as hot as possible *)
  in
  List.iter partition_args closure;
  (!resC,!resR,!resH)
;;

let partition_closure (closure: rstep_unpartitioned list) : rstep_partitioned list =
  let filter_by (args:intexpr IntMap.t) (set:IntExprSet.t) : intexpr list =
    List.map snd (List.filter (fun ((i,expr):int*intexpr) -> IntExprSet.mem (IVar (IArg i)) set) (IntMap.bindings args))
  in
  let (cold,reinit,hot) = compute_partition_map closure in
  let f ((name, rstep, _, breakdowns) : rstep_unpartitioned) : rstep_partitioned =
    let g ((condition, freedoms, desc, desc_with_calls):breakdown) : breakdown = 
      let h (e:spl) : spl =
	match e with
	| Call (callee, args) ->
  	  ActualCall(callee, (filter_by args (StringMap.find callee cold)), (filter_by args (StringMap.find callee reinit)), (filter_by args (StringMap.find callee hot)))
	| x -> x
      in
      (condition, freedoms, desc, (meta_transform_spl_on_spl BottomUp h) desc_with_calls) in
    (name, rstep, (StringMap.find name cold), (StringMap.find name reinit), (StringMap.find name hot), (List.map g breakdowns))
  in
  List.map f closure
;;

let lib = partition_closure closure
;;

let f ((name, rstep, cold, reinit, hot, breakdowns ): rstep_partitioned) : _ =
  print_string ("NAME\t\t"^name^"\n");
  print_string ("RS\t\t"^(string_of_spl rstep)^"\n");
  print_string ("COLD\t\t"^(String.concat ", " (List.map string_of_intexpr (IntExprSet.elements cold)))^"\n");
  print_string ("REINIT\t\t"^(String.concat ", " (List.map string_of_intexpr (IntExprSet.elements reinit)))^"\n");
  print_string ("HOT\t\t"^(String.concat ", " (List.map string_of_intexpr (IntExprSet.elements hot)))^"\n");
  let g ((condition, freedoms, desc, desc_with_calls):breakdown) : _ =
    print_string ("APPLICABLE\t"^(string_of_boolexpr condition)^"\n");
    print_string ("FREEDOM\t\t"^(String.concat ", " (List.map string_of_intexpr_intexpr freedoms))^"\n");
    print_string ("DESCEND\t\t"^(string_of_spl desc)^"\n");
    print_string ("DESCEND - CALLS\t"^(string_of_spl desc_with_calls)^"\n");
  in
  List.iter g breakdowns;
  print_string ("\n")
  
in
List.iter f lib
;;

type envexpr =
  SimpleEnv of int
;;

let string_of_envexpr (e:envexpr) : string =
  match e with
    SimpleEnv i -> "child"^(string_of_int i)
;;

type statement =
| IntDecl of intexpr
| IntAssign of intexpr * intexpr
| EnvAssign of envexpr * string
| EnvCall of string * envexpr * string
| If of boolexpr * statement * statement
| Error of string
| Chain of statement list
| Loop of intexpr * intexpr * statement
| Class of string * intexpr list * intexpr list * statement
;;

type var = 
| Int of string
;;

let rec type_of (v:var) : string =
  match v with
  |Int -> "int"
;;

let rec white (n:int) : string =
  if (n <= 0) then
    ""
  else
    " "^(white (n-1))
;;

let rec string_of_statement (n:int) (stmt:statement) : string =
  match stmt with
  | IntDecl x -> (white n)^"int "^(string_of_intexpr x)^";\n"
  | IntAssign (left, right) -> (white n)^(string_of_intexpr left) ^ " = " ^ (string_of_intexpr right) ^ ";\n"
  | EnvAssign(env,s) -> (white n)^(string_of_envexpr env)^ " = " ^ s ^ ";\n"
  | EnvCall(name,env,s) -> (white n)^"cast <"^name^" *>("^(string_of_envexpr env) ^ ")" ^ s ^ ";\n"

  | If (cond, path_a, path_b) -> (white n)^"if ("^(string_of_boolexpr cond)^") {\n"^(string_of_statement (n+4) path_a)^(white n)^"} else {\n"^(string_of_statement (n+4) path_b)^(white n)^"}\n"
  | Error(str) -> (white n)^"error(\""^str^"\");\n"
  | Chain l -> String.concat "" (List.map (string_of_statement n) l)
  | Loop (i,c,exp) -> (white n)^"for(int "^(string_of_intexpr i)^" = 0; "^(string_of_intexpr i)^" < "^(string_of_intexpr c)^"; "^(string_of_intexpr i)^"++){\n"^(string_of_statement (n+4) exp)^(white n)^"}\n"
  | Class (name, ints, ctor_args, ctor) -> (white n)^"struct "^name^" : public RS {\n"^(String.concat "" (List.map (fun x -> string_of_statement (n+4) (IntDecl x)) ints))^(white (n+4))^name^"("^(String.concat "," (List.map (fun x->string_of_intexpr x) ctor_args))^"){\n"^(string_of_statement (n+8) ctor)^(white (n+4))^"};\n"^(white n)^"};\n"
;;

let class_of_rstep ((name, rstep, cold, reinit, hot, breakdowns): rstep_partitioned) : statement =
  let arguments_assign = Chain(List.map (fun x -> IntAssign(IVar(ITranscendental ("this->"^(string_of_intexpr x))),x)) (IntExprSet.elements cold)) in 
  Class(name, 
	IVar(ITranscendental("_rule"))::(IntExprSet.elements cold),
	(IntExprSet.elements cold),
	arguments_assign
  )
;;

let classes = List.map class_of_rstep lib
;;

print_string (String.concat "\n\n" (List.map (string_of_statement 0) classes))
;;



(* let print_prototype (lib: rstep_partitioned list) : _ = *)
(*   print_string ("static int isNotPrime(int a) {return 1;}\n"); *)
(*   print_string ("static int divisor(int a) {return 1;}\n"); *)
(*   print_string ("static void error(char* s) {throw s;}\n"); *)
(*   print_string ("struct RS {};\n\n"); *)
(*   let f ((name, rstep, cold, reinit, hot, breakdowns ): rstep_partitioned) : _= *)

(*     print_string ("struct "^name^" : public RS {\n"); *)
(*     print_string ("    int _rule;\n"); *)
(*     print_string ("    char *_dat;\n"); *)
(*     print_string (String.concat "" (List.map (fun x -> string_of_statement 4 (IntDecl x)) (IntExprSet.elements cold))); *)
    
(*     let g ((condition, freedoms, desc, desc_with_calls):breakdown) : _ = *)
(*       let h (l,r) = *)
(* 	print_string ((string_of_statement 4) (IntDecl(l))) *)
(*       in *)
(*       List.iter h freedoms *)
(*     in *)
(*     List.iter g breakdowns; *)

(*     print_string ("    "^name^"("^(String.concat ", " (List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements cold)))^");\n"); *)
(*     print_string ("    void compute("^(String.concat ", " ("double* Y"::"double* X"::(List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements hot))))^");\n"); *)
(*     print_string ("};\n\n") *)
(*   in *)
(*   List.iter f lib; *)
(* in *)
(* print_prototype lib *)
(* ;; *)

(* let print_content (lib: rstep_partitioned list) : _ = *)
(*   let f ((name,rstep, cold, reinit, hot, breakdowns ): rstep_partitioned) : _= *)
(*     print_string(name^"::"^name^"("^(String.concat ", " (List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements cold)))^") {\n"); *)
(*     let arguments_assign = Chain(List.map (fun x -> IntAssign(IVar(ITranscendental ("this->"^(string_of_intexpr x))),x)) (IntExprSet.elements cold)) in *)
(*     let envcount = ref 0 in *)
(*     let prepare_env_cons (rs:string) (cold:intexpr list) (reinit:intexpr list) : statement = *)
(*       envcount := !envcount + 1; *)
(*       EnvAssign (SimpleEnv !envcount,("new "^rs^"("^(String.concat ", " (List.map string_of_intexpr (List.append cold reinit)))^")")) *)
(*     in *)
(*     let rec prepare_cons (e:spl) : statement = *)
(*       match e with *)
(*       |Compose l -> Chain (List.map prepare_cons (List.rev l)) *)
(*       |ISum(i,count,spl) -> Loop(i,count,(prepare_cons spl)) (\*FIXME, there's some hoisting*\) *)
(*       |ActualCall(callee,cold,reinit,_) -> prepare_env_cons callee cold reinit *)
(*       | _ -> Error("nop") *)
(*     in *)
(*     let rulecount = ref 0 in *)
(*     let g (stmt:statement) ((condition,freedoms,desc,desc_with_calls):breakdown) : statement  = *)
(*       let freedom_assigns = List.map (fun (l,r)->IntAssign(l,r)) freedoms in *)
(*       rulecount := !rulecount + 1; *)
(*       If(condition,(Chain( freedom_assigns @ [IntAssign(IVar(ITranscendental "_rule"),IConstant !rulecount)] @ [prepare_cons desc_with_calls])),(Error("no applicable rules"))) *)
(*     in *)
(*     let code_cons = List.fold_left g (Error("no error")) breakdowns in *)
(*     print_string ((string_of_statement 4) (Chain (arguments_assign::[code_cons]))); *)
(*     print_string("}\n\n"); *)


(*     print_string ("void "^name^"::compute("^(String.concat ", " ("double* Y"::"double* X"::(List.map (fun x -> "int "^(string_of_intexpr x)) (IntExprSet.elements hot))))^"){\n"); *)
(*     let prepare_env_body (rs:string) (hot:intexpr list) : statement = *)
(*       envcount := !envcount + 1; (\*FIXME the arrays they are not correct*\) *)
(*       EnvCall (rs, SimpleEnv !envcount,("->compute("^(String.concat ", " (List.map string_of_intexpr hot))^")")) *)
(*     in *)
(*     let rec prepare_body (e:spl) : statement = *)
(*       match e with *)
(*       |Compose l -> Chain (List.map prepare_body (List.rev l)) *)
(*       |ISum(i,count,spl) -> Loop(i,count,(prepare_body spl)) (\*FIXME, there's some hoisting*\) *)
(*       |ActualCall(callee,_,_,hot) -> prepare_env_body callee hot *)
(*       | _ -> Error("nop") *)
(*     in *)
(*     let g (stmt:statement) ((condition,freedoms,desc,desc_with_calls):breakdown) : statement  = *)
(*       let decls = [Error("decl_buffer")] in *)
(*       envcount := 0; *)
(*       rulecount := !rulecount + 1; *)
(*       If(IntEqual(IVar(ITranscendental "_rule"),IConstant !rulecount),(Chain( decls @ [prepare_body desc_with_calls])),(Error("unknown rule"))) *)
(*     in *)
(*     rulecount := 0; *)
(*     let code_comp = List.fold_left g (Error("no error")) breakdowns in *)
(*     print_string (string_of_statement 4 code_comp); *)
(*     print_string("}\n\n"); *)
(*   in *)
(*   List.iter f lib *)
(* in *)
(* print_content lib *)






