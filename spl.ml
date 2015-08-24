open Util
;;

open Intexpr
;;

open Idxfunc
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

let rec string_of_spl (e : spl) : string =
  match e with
  | DFT (n) -> "DFT("^(string_of_intexpr n)^")"
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
  | GT(a, g, s, l) -> "GT("^(string_of_spl a)^", "^(string_of_idxfunc g)^", "^(string_of_idxfunc s)^", ["^(String.concat ";" (List.map string_of_intexpr l))^"])"
;;




(*********************************************
	 METARULES                 
*********************************************)

let meta_transform_spl_on_spl (recursion_direction: recursion_direction) (f : spl -> spl) : (spl -> spl) =
  (* print_string "meta_transform_spl_on_spl\n"; *)
  let z (g : spl -> spl) (e : spl) : spl = 
    match e with
    | Compose (l) -> Compose (List.map g l)
    | Tensor (l) -> Tensor (List.map g l)
    | ISum(v,c,a) -> ISum(v,c, (g a))
    | RS (l) -> RS(g l)
    | BB (l) -> BB(g l)
    | GT (a, c, s, l) -> GT(g a, c, s, l)
    | DFT _ | I _ | T _ | L _ | Diag _ | S _ | G _ | UnpartitionnedCall _  | F _ | ISumReinitCompute _ | Compute _ | ISumReinitConstruct _ | Construct _-> e
    | _ -> failwith("meta_transform_spl_on_spl, not handled: "^(string_of_spl e))         
  in
  recursion_transform recursion_direction f z
;;

let meta_transform_idxfunc_on_spl (recursion_direction: recursion_direction) (f : idxfunc -> idxfunc) : (spl -> spl) =
  (* print_string "meta_transform_idxfunc_on_spl\n"; *)
  let g = meta_transform_idxfunc_on_idxfunc recursion_direction f in
  meta_transform_spl_on_spl recursion_direction ( function
  | G(l) -> G(g l) 
  | S(l) -> S(g l) 
  | Diag(l) -> Diag( g l)
  | GT(a,c,s,l)->GT(a, g c, g s, l)
  | DFT _  | RS _ | I _ | Tensor _ | T _ | L _ | Compose _ | ISum _ | F _ | BB _ as e -> e
  | e -> failwith("meta_transform_idxfunc_on_spl, not handled: "^(string_of_spl e))         		
  )
;;

let meta_transform_intexpr_on_spl (recursion_direction: recursion_direction) (f : intexpr -> intexpr) : (spl -> spl) =
  (* print_string "meta_transform_intexpr_on_spl\n"; *)
  let g = meta_transform_intexpr_on_intexpr recursion_direction f in
  let intexprs_in_spl (e : spl) : spl = 
    match e with
    | Compose _ | Tensor _ | RS _ | Diag _ | G _| S _ -> e
    | ISum(v,c,a) -> ISum(g v,g c,a)
    | GT(v, c, s, l) -> GT(v, c, s, (List.map g l))
    | L (n, m) -> L(g n, g m)
    | T (n, m) -> T(g n, g m)
    | I n -> I(g n)
    | DFT n -> DFT (g n)
    | BB _ -> e
    | UnpartitionnedCall _ -> e
    | PartitionnedCall _ -> e
    | F _ -> e
    | ISumReinitCompute _| Compute _ | ISumReinitConstruct _ | Construct _ -> assert false
    | _ -> failwith("meta_transform_intexpr_on_spl, not handled: "^(string_of_spl e))         		
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

let meta_collect_idxfunc_on_spl (f : idxfunc -> 'a list) : (spl -> 'a list) =
  meta_collect_spl_on_spl ( function
  | G(l) -> f l
  | S(l) -> f l
  | Diag(l) -> f l
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


let meta_iter_idxfunc_on_spl (f : idxfunc -> unit) : (spl -> unit) =
  fun (e : spl) ->
    ignore((meta_collect_idxfunc_on_spl (fun (e:idxfunc) -> f e;[])) e)
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

(*********************************************
	 RANGE AND DOMAIN                 
*********************************************)
let rec range (e :spl) : intexpr = 
  match e with
    DFT(n) -> n
  | Tensor (list) -> IMul(List.map range list)
  | GT (a, g, s, l) -> IMul(range a :: l)
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
  | Tensor (list) -> IMul(List.map domain list)
  | GT (a, g, s, l) -> IMul(domain a :: l)
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
	 SPL RULES                 
*********************************************)


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

let rule_tensor_to_GT : (spl -> spl) =
  let rec f (l : spl list) : spl list = 
    match l with
    | I(k) :: a :: tl ->
       GT(a
	 , FHH(domain a, domain a, IConstant 0, IConstant 1, [domain a])
	 , FHH(range a, range a, IConstant 0, IConstant 1, [range a])
	 , [k]) :: tl
    | a :: I(k) :: tl ->
       GT(a
	 , FHH(domain a, domain a, IConstant 0, k, [IConstant 1])
	 , FHH(range a, range a, IConstant 0, k, [IConstant 1])
	 , [k]) :: tl		      
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

let spl_rulemap =
  List.fold_left (fun (map) (name, rule) -> StringMap.add name rule map ) StringMap.empty ([
  ("Tensor to ISum", rule_tensor_to_isum);
  (* ("Tensor to GT", rule_tensor_to_GT); *)
  ("Remove unary tensor", rule_remove_unary_tensor);
  ("Remove unary compose", rule_remove_unary_compose); 
  ("Transform T into diag", rule_transorm_T_into_diag);
  ("Suck inside ISum", rule_suck_inside_isum);
  ("Suck inside RS", rule_suck_inside_RS);
  ("Flatten Compose", rule_flatten_compose);
  ("Compose Gather Gather", rule_compose_gather_gather);
  ("Compose Scatter Scatter", rule_compose_scatter_scatter);
  ("Compose Gather Diag", rule_compose_gather_diag);
  ("Compose BB Diag", rule_compose_BB_diag);
  ("Compose BB Gather", rule_compose_BB_gather);
  ("Compose Scatter BB", rule_compose_scatter_BB);
]
 @(List.map (fun (name,rule) -> ("Lifted "^name, meta_transform_intexpr_on_spl BottomUp rule)) (StringMap.bindings intexpr_rulemap))
 @(List.map (fun (name,rule) -> ("Lifted "^name, meta_transform_idxfunc_on_spl BottomUp rule)) (StringMap.bindings idxfunc_rulemap))
)
;;
   
