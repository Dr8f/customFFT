exception AlgoNotApplicable of string
;;

open Util
;;

open Spl
;;

open Intexpr
;;
  
open Boolexpr
;;
 
let gen_freedom_var =
object 
  val tbl = ref 0;
  method get () : intexpr = 
    tbl := !tbl + 1;
    IFreedom !tbl
end
;;


let within_GT_rank_one (l:spl list) : bool =
  print_string("ctx: "^(String.concat " ||| " (List.map Spl.string_of_spl l))^"\n");
  let mylist = List.flatten (List.map collect_GT l) in
  let n = List.length (mylist) in
  if (n=0) then 
    true
  else 
    (
      if (n=1) then
	match List.hd mylist with
	| GT(_,_,_,l) -> List.length(l) <=1
	| _ -> assert false
      else
	false
    )
;;
  
let algo_cooley_tukey : spl -> boolexpr * (intexpr*intexpr) list * spl =
  function (e:spl) ->
    let conditions = ref [] in
    let freedoms = ref [] in
    let g (ctx:spl list) (s:spl) : spl =
      match s with
      |DFT n when (within_GT_rank_one ctx) -> 	    
	conditions := Not(IsPrime(n)) :: !conditions;
	let k = gen_freedom_var#get () in
	freedoms := (k, IDivisor n) :: !freedoms;
	let m = IDivPerfect(n, k) in
	Compose([Tensor( [DFT(k); I(m)]); T(n, m); Tensor([I(k); DFT(m)]); L(n,k)])
      | DFT _ ->
	raise (AlgoNotApplicable "Cooley Tukey not applicable within GT")
      | x -> 
	x
    in
    let f = meta_transform_ctx_spl_on_spl BottomUp g in
    ((And !conditions), !freedoms, f e)
;;  

(* this is for debug only *)
let algo_dft_itself : spl -> boolexpr * (intexpr*intexpr) list * spl =
  function (e:spl) ->
	   let f = meta_transform_spl_on_spl BottomUp ( function
							|DFT n -> DFT n
							| x -> x) in
	   (True, [], f e)
;;

let algo_dft_base : spl -> boolexpr * (intexpr*intexpr) list * spl =
  function (e:spl) ->
    let conditions = ref [] in
    let f = meta_transform_spl_on_spl BottomUp ( function
      |DFT n ->
	conditions := Equal(n,IConstant(2)) :: !conditions;
	BB(F(2))

      | Spl.GT(_,_,_,l) as e ->  
	if (List.length l >1) then
	  raise (AlgoNotApplicable "Cannot apply a base case where there is a rank 2 or more GT, all freedoms have not been resolved")
	else
	  e
	
      (* (\* GT rank 1 downrank, should later be part of all base cases *\) *)
      (* | Spl.GT(a, g, s, v::[]) ->  *)
      (* 	let i = Intexpr.gen_loop_counter#get () in  *)
      (* 	ISum(i, v, Compose([S(Idxfunc.FDown(s, i, 0));Spl.Down(a, i, 0);G(Idxfunc.FDown(g, i, 0))])) *)
				      
      | x -> x) in
    ((And !conditions), [], f e)
;;
