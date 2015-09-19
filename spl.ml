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
| Down of spl * intexpr * int
| PreComp of spl
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
  | Down(s,l,d) -> "Down("^(string_of_spl s)^", "^(string_of_intexpr l)^", "^(string_of_int d)^")"  
  | PreComp(s) -> "PreComp("^(string_of_spl s)^")"
;;




(*********************************************
	 METARULES                 
*********************************************)

let meta_transform_ctx_spl_on_spl (recursion_direction: recursion_direction) : (spl list -> spl -> spl) -> spl -> spl =
  let z (g : spl -> spl) (_:spl list) (e : spl) : spl =
    match e with
    | Compose (l) -> Compose (List.map g l)
    | Tensor (l) -> Tensor (List.map g l)
    | ISum(v,c,a) -> ISum(v,c, (g a))
    | RS (l) -> RS(g l)
    | BB (l) -> BB(g l)
    | GT (a, c, s, l) -> GT(g a, c, s, l)
    | DFT _ | I _ | T _ | L _ | Diag _ | S _ | G _ | UnpartitionnedCall _  | F _ | ISumReinitCompute _ | Compute _ | ISumReinitConstruct _ | Construct _ | PartitionnedCall _ -> e
    | Down(s,a,b) -> Down(g s, a, b)
    | PreComp(s) -> PreComp(g s)
  in
  recursion_transform_ctx recursion_direction z
;;

let meta_transform_spl_on_spl (recursion_direction: recursion_direction) (z: spl -> spl) : spl -> spl =
  meta_transform_ctx_spl_on_spl recursion_direction (fun _ -> z) 
;;


let meta_transform_ctx_idxfunc_on_spl (recursion_direction: recursion_direction) (f : spl list -> idxfunc list -> idxfunc -> idxfunc) : (spl -> spl) =
  (* print_string "meta_transform_ctx_idxfunc_on_spl\n"; *)
  let h (ctx:spl list) (e:spl) : spl = 
    let g = meta_transform_ctx_idxfunc_on_idxfunc recursion_direction (f ctx) in
    match e with
    | G(l) -> G(g l) 
    | S(l) -> S(g l) 
    | Diag(l) -> Diag( g l)
    | GT(a,c,s,l)->GT(a, g c, g s, l)
    | DFT _  | RS _ | I _ | Tensor _ | T _ | L _ | Compose _ | ISum _ | F _ | BB _ | Down _ | PreComp _ | Compute _ | ISumReinitCompute _ as e -> e
    | Construct(a,b,c,d) -> Construct(a,b,c,(List.map g d))
    | ISumReinitConstruct(a, b, c ,d , ee, f, gg) -> ISumReinitConstruct(a, b, c, d, ee, f, List.map g gg)
    | e -> failwith("meta_transform_idxfunc_on_spl, not handled: "^(string_of_spl e))         	
  in
  meta_transform_ctx_spl_on_spl recursion_direction h
;;

let meta_transform_idxfunc_on_spl (recursion_direction: recursion_direction) (z : idxfunc -> idxfunc) : (spl -> spl) =
  meta_transform_ctx_idxfunc_on_spl recursion_direction (fun _ _ -> z)
;;

let meta_transform_ctx_intexpr_on_spl (recursion_direction: recursion_direction) (f : spl list -> idxfunc list -> intexpr list -> intexpr -> intexpr) : (spl -> spl) =
  (* print_string "meta_transform_ctx intexpr_on_spl\n"; *)
  let h (ctx:spl list) (e : spl) : spl = 
    let g = meta_transform_ctx_intexpr_on_intexpr recursion_direction (f ctx []) in
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
    | ISumReinitConstruct(a, b, c ,d , ee, f, gg) -> ISumReinitConstruct(a, g b, g c, d, List.map g ee, List.map g f, gg)
    | ISumReinitCompute(a,b,c,d,ee,f,gg) -> ISumReinitCompute(a, g b, g c, d, List.map g ee, g f, g gg)
    | Construct(a,b,c,d) -> Construct(a,b,(List.map g c),d)
    | Compute(a,b,c,d,e) -> Compute(a,b,(List.map g c),g d,g e)
    | Down(s,l,d) -> Down(s, g l, d)
    | PreComp(s) -> PreComp(s)
    (* | _ -> failwith("meta_transform_intexpr_on_spl, not handled: "^(string_of_spl e))         		 *)
  in
  fun (e : spl) ->
    let z (splctx: spl list) (idxfuncctx:idxfunc list) : idxfunc -> idxfunc =
      let zz (hh:idxfunc list) : intexpr list -> intexpr -> intexpr =
	f splctx (idxfuncctx@hh) in
      (meta_transform_ctx_intexpr_on_idxfunc recursion_direction zz)      
    in
    let res = (meta_transform_ctx_idxfunc_on_spl recursion_direction z e) in
  (meta_transform_ctx_spl_on_spl recursion_direction h) res
;;

let meta_transform_intexpr_on_spl (recursion_direction: recursion_direction) (z : intexpr -> intexpr) : (spl -> spl) =
  meta_transform_ctx_intexpr_on_spl recursion_direction (fun _ _ _ -> z)
;;

let meta_collect_ctx_spl_on_spl (f : spl list -> spl -> 'a list) : (spl -> 'a list) =
  let z (g : spl -> 'a list) (_:spl list) (e : spl) : 'a list =
    match e with
      Compose l | Tensor l -> List.flatten (List.map g l)
    | ISum(_,_,a) | GT(a,_,_,_) -> g a
    | RS a -> g a
    | _ -> []
  in
  recursion_collect_ctx z f
;;

let meta_collect_spl_on_spl (z : spl -> 'a list) : (spl -> 'a list) =
  meta_collect_ctx_spl_on_spl (fun _ -> z)
;;

let meta_collect_ctx_idxfunc_on_spl (f : spl list -> idxfunc -> 'a list) : (spl -> 'a list) =
  let z (ctx:spl list) (e:spl) : 'a list = 
    match e with
    | G(l) -> f ctx l
    | S(l) -> f ctx l
    | Diag(l) -> f ctx l
    | GT(_,a,b,_)->(f ctx a)@(f ctx b)
    | _ -> []
  in
  meta_collect_ctx_spl_on_spl z
;;

let meta_collect_idxfunc_on_spl (z : idxfunc -> 'a list) : (spl -> 'a list) =
  meta_collect_ctx_idxfunc_on_spl (fun _ -> z)
;;

let meta_collect_intexpr_on_spl (f : intexpr -> 'a list) : (spl -> 'a list) =
  let direct_from_spl (ff : intexpr -> 'a list) (e : spl) : 'a list =
    match e with
      Compose _ | Tensor _ | RS _ | Diag _ | G _| S _ | UnpartitionnedCall _ | PartitionnedCall _ -> []
    | ISum(n, m, _) | L (n, m) | T (n, m)-> (ff n) @ (ff m)
    | I n  | DFT n -> ff n
    | GT (_, _, _, l) -> List.flatten(List.map ff l)
    | ISumReinitCompute _| Compute _ | ISumReinitConstruct _ | Construct _ -> assert false
    | _ -> failwith("meta_collect_intexpr_on_spl, not handled: "^(string_of_spl e))         		
  in
  fun (e : spl) ->
    let ff = meta_collect_intexpr_on_intexpr f in
    ((meta_collect_spl_on_spl (direct_from_spl ff )) e)
    @ ((meta_collect_idxfunc_on_spl (meta_collect_intexpr_on_idxfunc ff)) e)
;;

let meta_iter_ctx_spl_on_spl (f : spl list -> spl -> unit) : (spl -> unit) =
  fun (e : spl) ->
    ignore((meta_collect_ctx_spl_on_spl (fun (ctx:spl list) (e:spl) -> f ctx e;[])) e)
;;

let meta_iter_spl_on_spl (z : spl -> unit) : (spl -> unit) =
  meta_iter_ctx_spl_on_spl (fun _ -> z)
;;

let meta_iter_ctx_idxfunc_on_spl (f :spl list -> idxfunc -> unit) : (spl -> unit) =
  fun (e : spl) ->
    ignore((meta_collect_ctx_idxfunc_on_spl (fun (ctx:spl list) (e:idxfunc) -> f ctx e;[])) e)
;;

let meta_iter_idxfunc_on_spl (f : idxfunc -> unit) : (spl -> unit) =
  meta_iter_ctx_idxfunc_on_spl (fun _ -> f)
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
let rec spl_range (e :spl) : intexpr = 
  match e with
  | Tensor (list) -> IMul(List.map spl_range list)
  | GT (a, _, _, l) -> IMul(spl_range a :: l)
  | I(n) | T(n, _) | L(n, _) | DFT(n) -> n
  | Compose ( list ) -> spl_range (List.hd list)
  | S (f) -> func_range f
  | G (f) | Diag (f) -> func_domain f
  | ISum (_, _, s) | RS (s) | BB(s) -> spl_range s
  | F(n) -> IConstant n
  | ISumReinitCompute (_, _, _, _, _, r, _)  | Compute (_,_,_,r,_) -> r
  | ISumReinitConstruct _ | Construct _ | UnpartitionnedCall _ | PartitionnedCall _ -> assert false
  | Down(a,_,_) -> spl_range a
  | PreComp(a) -> spl_range a
;;    

let rec spl_domain (e :spl) : intexpr = 
  match e with
  | F(n) -> IConstant n
  | Tensor (list) -> IMul(List.map spl_domain list)
  | GT (a, _, _, l) -> IMul(spl_domain a :: l)
  | DFT(n) | I(n) | T(n, _) | L(n, _) -> n
  | Compose ( list ) -> spl_domain (List.hd (List.rev list))
  | S (f) -> func_domain f
  | G (f) -> func_range f
  | Diag (f) -> func_domain f (* by definition a diag range is equal to a diag domain. However the range of the function is larger but noone cares since its precomputed*)
  | ISum (_, _, s) | RS (s) | BB(s)-> spl_domain s
  | UnpartitionnedCall _ | PartitionnedCall _ | ISumReinitConstruct _ | Construct _ -> assert false
  | ISumReinitCompute (_, _, _, _, _, _, d)   | Compute (_,_,_,_,d) -> d
  | Down(a,_,_) -> spl_domain a
  | PreComp(a) -> spl_domain a

;;    

(*********************************************
	 SPL RULES                 
*********************************************)


let rule_tensor_to_isum : (spl -> spl) =
  let rec f (l : spl list) : spl list = 
    match l with
      I(k) :: a :: tl ->
	let i = gen_loop_counter#get () in 
	f ( ISum(i, k, Compose( [S(FH(spl_range a, IMul([spl_range a; k]), IMul([spl_range a; i]), IConstant 1)); a ; G(FH(spl_domain a, IMul([spl_domain a; k]), IMul([spl_domain a; i]), IConstant 1)) ] )) :: tl)
    | a :: I(k) :: tl -> 
      let i = gen_loop_counter#get () in 
      f ( ISum(i, k, Compose( [S(FH(spl_range a, IMul([spl_range a; k]), i, k)); a; G(FH(spl_domain a, IMul([spl_domain a; k]), i, k)) ] )) :: tl)
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
	 , FHH(spl_domain a, spl_domain a, IConstant 0, IConstant 1, [spl_domain a])
	 , FHH(spl_range a, spl_range a, IConstant 0, IConstant 1, [spl_range a])
	 , [k]) :: tl
    | a :: I(k) :: tl ->
       GT(a
	 , FHH(spl_domain a, spl_domain a, IConstant 0, k, [IConstant 1])
	 , FHH(spl_range a, spl_range a, IConstant 0, k, [IConstant 1])
	 , [k]) :: tl		      
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_tensorize_spl BottomUp f
;;

let rule_suck_inside_GT : (spl -> spl) =
  let rec f (l : spl list) : spl list = 
  match l with
  | GT(a, g, s, v)::L(n,k)::tl -> f ( GT( a, FCompose([FUp(FL(n,k));g]), s, v)::tl )
  | GT(a, g, s, v)::Diag(d)::tl -> f ( GT( Compose([a;Diag(FCompose([FUp(d); g]))]), g, s, v)::tl )
  | a::tl -> a :: (f tl)
  | [] -> []
  in
  meta_compose_spl BottomUp f
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
  
let rule_warp_GT_RS : (spl -> spl) =
  meta_transform_spl_on_spl BottomUp (function 
  | GT(RS a,g,s,l) -> RS(GT(a,g,s,l))
  | x -> x
)
;;

let rule_pull_precompute : (spl -> spl) =
  meta_transform_spl_on_spl BottomUp (function 
  | BB(PreComp(a)) -> PreComp(a)
  | GT(PreComp(a),g,s,l) -> 
    if (List.length l == 1) then 
      PreComp(GT(a,FNil, FHH(spl_domain a, spl_domain a, IConstant 0, IConstant 1, [spl_domain a]),l))
    else
      failwith("not implemented yet")
  | x -> x
  )
;;


let rule_suck_inside_RS : (spl -> spl) =
  let rec f (l : spl list) : spl list = 
  match l with
  | RS(a)::(Diag _ as b)::tl -> f (RS(Compose([a;b])) :: tl)
  | RS(a)::(G _ as b)::tl -> f (RS(Compose([a;b])) :: tl)
  | RS(a)::(L _ as b)::tl -> f (RS(Compose([a;b])) :: tl)
  | (S _ as a)::RS(b)::tl -> f (RS(Compose([a;b])) :: tl) 
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

let rule_distribute_downrank_spl : (spl -> spl) =
  meta_transform_spl_on_spl TopDown ( function
  | Down (Compose list, j, l) -> Compose( List.map (fun x-> Down(x, j, l)) list)
  | Down (BB(x),j,l) -> BB(Down(x,j,l))
  | Down (F(i),_,_) ->F(i)
  | Down (Diag(f),j,l) ->Diag(FDown(f,j,l))
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

let rule_precompute_compose : (spl -> spl) =
  let rec f (l : spl list) : spl list = 
    match l with
    | F _ :: PreComp(a)::tl -> f (PreComp(a)::tl)
    | PreComp a :: G _ :: tl -> f (PreComp a :: tl)
    | S _ :: PreComp a :: tl -> f (PreComp( Compose( [S(FH(spl_domain a, spl_range a, IConstant 0, IConstant 1)) ; a] )) :: tl)   

    | a :: b ::tl -> a :: f(b :: tl)
    | x -> x
  in
  meta_compose_spl BottomUp f
;;  

let rule_gath_fnil : (spl -> spl) =
  let rec f (l : spl list) : spl list = 
    match l with
    | a :: G(FNil) :: tl -> f (a::tl)
    | a :: b :: tl -> a:: f (b::tl)
    | x -> x
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
  (* ("Tensor to ISum", rule_tensor_to_isum); *)
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
  ("Distribute FDown", rule_distribute_downrank_spl);
  ("Rule Precompute Compose", rule_precompute_compose);
  ("Rule Gath FNil", rule_gath_fnil);
  ("Rule Pull Precompute", rule_pull_precompute);

  (* TODO 
     Currently breaks because DFT is applied within GT
     Should introduce GT downrank to verify that RS4 and RS 5 (page 88) are properly generated and that the all code runs
     Then introduce DFT within GT to breakdown the rest
   *)
  ("Tensor to GT", rule_tensor_to_GT);
  ("rule_suck_inside_GT", rule_suck_inside_GT);
  ("rule_warp_GT_RS", rule_warp_GT_RS);
]
 @(List.map (fun (name,rule) -> ("Lifted "^name, meta_transform_intexpr_on_spl BottomUp rule)) (StringMap.bindings intexpr_rulemap))
 @(List.map (fun (name,rule) -> ("Lifted "^name, meta_transform_idxfunc_on_spl BottomUp rule)) (StringMap.bindings idxfunc_rulemap))
)
;;
   
let simplify_spl (f:spl) : spl = 
  apply_rewriting_rules spl_rulemap f
;;
