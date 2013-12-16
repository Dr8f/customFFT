open Spl
;;

(**********************
      ALGO
***********************)

let gen_freedom_var =
object 
  val tbl = ref 0;
  method get () : intexpr = 
    tbl := !tbl + 1;
    IFreedom !tbl
end
;;


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

