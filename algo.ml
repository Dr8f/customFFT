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


let count_GT (l:spl list) : int =
  print_string("ctx: "^(String.concat " ||| " (List.map Spl.string_of_spl l))^"\n");
  let collect_GT: spl -> spl list =
    meta_collect_spl_on_spl ( function
			      | GT(_) as x -> [x]
			      | _ -> []
			    )
  in
  let n = 
    List.length (List.flatten (List.map collect_GT l)) in
  print_string ("count:"^(string_of_int n)^"\n\n");
  n
;;
  
let algo_cooley_tukey : spl -> boolexpr * (intexpr*intexpr) list * spl =
  function (e:spl) ->
    let conditions = ref [] in
    let freedoms = ref [] in
    let g (ctx:spl list) (s:spl) : spl =
      match s with
      |DFT n when (count_GT ctx) < 1 -> 	    
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
    let f = meta_transform_spl_on_spl_context BottomUp g in
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
	  
      (* GT rank 1 downrank, should later be part of all base cases *)
      | Spl.GT(a, g, s, v::[]) -> 
	let i = Intexpr.gen_loop_counter#get () in 
	ISum(i, v, Compose([S(Idxfunc.FDown(s, i, 0));Spl.Down(a, i, 0);G(Idxfunc.FDown(g, i, 0))]))
				      
      | x -> x) in
    ((And !conditions), [], f e)
;;
