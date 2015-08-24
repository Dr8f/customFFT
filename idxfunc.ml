open Util
;;

open Intexpr
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

let rec string_of_idxfunc (e : idxfunc) : string =
  match e with
    FH(src, dest, j,k) -> "FH("^(string_of_intexpr src)^","^(string_of_intexpr dest)^","^(string_of_intexpr j)^","^(string_of_intexpr k)^")"
  | FL(j,k) -> "FL("^(string_of_intexpr j)^","^(string_of_intexpr k)^")"      
  | FD(n,k) -> "FD("^(string_of_intexpr n)^","^(string_of_intexpr k)^")"      
  | FCompose(l) -> optional_short_infix_list_print "FCompose" " . " l string_of_idxfunc

  | Pre(l) -> "Pre("^(string_of_idxfunc l)^")"
  | PreWrap(n, l, funcs, d) -> "PreWrap(\""^n^"\", ["^(String.concat "; " (List.map string_of_intexpr l))^"], ["^(String.concat "; " (List.map string_of_idxfunc funcs))^"], "^(string_of_intexpr d)^")"
  | FArg(n, d) -> "FArg(\""^n^"\", "^(string_of_intexpr d)^")"
  | FHH(d, r, b, s, vs) -> "FHH("^(string_of_intexpr d)^", "^(string_of_intexpr r)^", "^(string_of_intexpr b)^" , "^(string_of_intexpr s)^", ["^(String.concat "; " (List.map string_of_intexpr vs))^"] )"
;;

let meta_transform_idxfunc_on_idxfunc (recursion_direction: recursion_direction) (f : idxfunc -> idxfunc) : (idxfunc -> idxfunc) =
  (* print_string "meta_transform_idxfunc_on_idxfunc\n"; *)
  let z (g : idxfunc -> idxfunc) (e : idxfunc) : idxfunc = 
    match e with 
    | FCompose (l) -> FCompose (List.map g l)
    | Pre(l) -> Pre(g l)
    | PreWrap(a, b, c, d) -> PreWrap(a,b, (List.map g c), d)
    | FHH _ | FD _ | FH _ | FL _ | FArg _ -> e
    | _ -> failwith("meta_transform_idxfunc_on_idxfunc, not handled: "^(string_of_idxfunc e))         		
  in
  recursion_transform recursion_direction f z
;;

let meta_transform_intexpr_on_idxfunc (recursion_direction: recursion_direction) (f : intexpr -> intexpr) : (idxfunc -> idxfunc) =
  (* print_string "meta_transform_intexpr_on_idxfunc\n"; *)
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
    | FHH (a, b, c, d, vs) -> let ga = g a in
  			     let gb = g b in
  			     let gc = g c in
			     let gd = g d in			     
  			     FHH (ga, gb, gc, g d, List.map g vs)
    | _ -> failwith("meta_transform_intexpr_on_idxfunc, not handled: "^(string_of_idxfunc e))         		
  in
  meta_transform_idxfunc_on_idxfunc recursion_direction z
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

let meta_collect_intexpr_on_idxfunc (f : intexpr -> 'a list) : (idxfunc -> 'a list) = 
  meta_collect_idxfunc_on_idxfunc ( function
  | FH (a, b, c, d) -> (f a) @ (f b) @ (f c) @ (f d)
  | FL(n, m) | FD(n,m) -> (f n) @ (f m)
  | _ -> []
  )
;;

let meta_iter_idxfunc_on_idxfunc (f : idxfunc -> unit) : (idxfunc -> unit) =
  fun (e : idxfunc) ->
    ignore((meta_collect_idxfunc_on_idxfunc (fun (e:idxfunc) -> f e;[])) e)
;;

let meta_iter_intexpr_on_idxfunc(f : intexpr -> unit) : (idxfunc -> unit) =
  fun (e : idxfunc) ->
    ignore(meta_collect_intexpr_on_idxfunc (fun (e:intexpr) -> f e;[]) e)
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
| PreWrap(_,_,_,d) -> d
| FArg (_,d)->d
;;

let meta_compose_idxfunc (recursion_direction : recursion_direction) (f : idxfunc list -> idxfunc list) : (idxfunc -> idxfunc) =
  meta_transform_idxfunc_on_idxfunc recursion_direction ( function 
  | FCompose (l) -> FCompose (f l) 
  | x -> x)
;;

let rule_flatten_fcompose : (idxfunc -> idxfunc) =
  let rec f (l : idxfunc list) : idxfunc list = 
  match l with
    FCompose(a)::tl -> f (a @ tl)
  | a::tl -> a :: (f tl)
  | [] -> []
  in
  meta_compose_idxfunc BottomUp f
;;  

let rule_remove_unary_fcompose : (idxfunc -> idxfunc) =
  meta_transform_idxfunc_on_idxfunc BottomUp ( function
  |FCompose ([a]) -> a
  | x -> x)
;;

let rule_compose_FL_FH : (idxfunc -> idxfunc) =
  let rec f (l : idxfunc list) : idxfunc list =
  match l with
    FL(n1,k) :: FH(m1,n2,IMul(m2::multl), IConstant 1) :: tl when m1 = m2 -> f (FH(m1, n2, IMul(multl), k) :: tl) 
    (*n1 = n2 is not checked because n could be mul(k,m) *)
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_compose_idxfunc BottomUp f
;;

let rule_compose_FH_FH : (idxfunc -> idxfunc) =
  let rec f (l : idxfunc list) : idxfunc list =
  match l with
    FH(gn1,gnp,bp,sp) :: FH(n,gn2,b,s) :: tl -> f (FH(n, gnp, IPlus([bp;IMul([sp; b])]), IMul([sp; s])) :: tl)
    (*gn1 = gn2 is not checked because that could be non-obvious*)
    | a::tl -> a :: (f tl)
    | [] -> []
  in
  meta_compose_idxfunc BottomUp f
;;

let rule_compose_FHH_FHH : (idxfunc -> idxfunc) =
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
  
let rule_suck_inside_pre : (idxfunc -> idxfunc) = 
  let rec f (l : idxfunc list) : idxfunc list =
  match l with
    Pre(a)::b::tl -> f (Pre(FCompose([a;b])) :: tl)
  | a::tl -> a :: (f tl)
  | [] -> []
  in
  meta_compose_idxfunc BottomUp f  
;;

  
let rule_distribute_uprank : (idxfunc -> idxfunc) =
  meta_transform_idxfunc_on_idxfunc TopDown ( function
  | FUp (FCompose list) -> FCompose( List.map (fun x-> FUp(x)) list)
  | x -> x)
;;

let rule_distribute_downrank : (idxfunc -> idxfunc) =
  meta_transform_idxfunc_on_idxfunc TopDown ( function
  | FDown (FCompose list, j, l) -> FCompose( List.map (fun x-> FDown(x, j, l)) list)
  | x -> x)
;;

let rule_uprank_FHH : (idxfunc -> idxfunc) =
  meta_transform_idxfunc_on_idxfunc TopDown ( function
  | FUp (FHH(d,r,b,s,vs)) -> FHH(d,r,b,s,(IConstant 0::vs))
  | x -> x)
;;

let rule_downrank_FHH : (idxfunc -> idxfunc) =
  let rec extract (l:int) (vs:intexpr list) : intexpr * intexpr list =
    let (x::xs)=vs in
    if (l=0) then
      (x, xs)
    else
      let (a,b) = extract (l-1) xs in
      (a,x::b)
  in
  meta_transform_idxfunc_on_idxfunc TopDown ( function
  | FDown (FHH(d,r,b,s,vs), j , l) ->
     let(content,remainder)= extract l vs in
     FHH(d,r, IPlus([b;IMul([content;j])]), s, remainder)
  | x -> x)
;;

let idxfunc_rulemap = 
  List.fold_left (fun (map) (name, rule) -> StringMap.add name rule map ) StringMap.empty (
		   [
		     ("Flatten FCompose", rule_flatten_fcompose);
		     ("Remove unary fcompose", rule_remove_unary_fcompose);
		     ("Rule suck inside pre", rule_suck_inside_pre);
		     ("FCompose FHH with FHH", rule_compose_FHH_FHH);
		     ("Compose_l_h", rule_compose_FL_FH);
		     ("Compose_h_h", rule_compose_FH_FH);
		     ("Distribute uprank", rule_distribute_uprank);
		     ("Distribute downrank", rule_distribute_downrank);
		     ("Downrank FHH", rule_downrank_FHH);
		     ("Uprank FHH", rule_uprank_FHH);
		   ]
		   @(List.map (fun (name,rule) -> ("Lifted "^name, meta_transform_intexpr_on_idxfunc BottomUp rule)) (StringMap.bindings intexpr_rulemap))
)
;;
