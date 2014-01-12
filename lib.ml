(******    TYPES    *******)

open Spl
;;

module SplMap = Map.Make (struct
  type t = spl
  let compare = Pervasives.compare
end)

module IdxFuncMap = Map.Make (struct
  type t = idxfunc
  let compare = Pervasives.compare
end)

module IntExprSet = Set.Make (struct
  type t = intexpr
  let compare = Pervasives.compare
end)
;;

type breakdown = (boolexpr * (intexpr * intexpr) list * spl * spl)
;;

type rstep_unpartitioned = (string * spl * IntExprSet.t * breakdown list )
;;

type closure = rstep_unpartitioned list
;;

type breakdown_enhanced = (boolexpr * (intexpr * intexpr) list * spl * spl * spl * spl)
;;

type rstep_partitioned = (string * spl * IntExprSet.t * IntExprSet.t * IntExprSet.t * breakdown_enhanced list)
;;

type lib = rstep_partitioned list
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


(******** PRINTING *******)

let string_of_breakdown_enhanced ((condition, freedoms, desc, desc_with_calls, desc_with_calls_cons, desc_with_calls_comp):breakdown_enhanced) : string = 
  "APPLICABLE\t\t"^(string_of_boolexpr condition)^"\n"
  ^"FREEDOM\t\t\t"^(String.concat ", " (List.map string_of_intexpr_intexpr freedoms))^"\n"
  ^"DESCEND\t\t\t"^(string_of_spl desc)^"\n"
  ^"DESCEND - CALLS\t\t"^(string_of_spl desc_with_calls)^"\n"
  ^"DESCEND - CALLS CONS\t"^(string_of_spl desc_with_calls_cons)^"\n"
  ^"DESCEND - CALLS COMP\t"^(string_of_spl desc_with_calls_comp)^"\n"
;;

let string_of_rstep_partitioned ((name, rstep, cold, reinit, hot, breakdowns ): rstep_partitioned) : string =
  "NAME\t\t\t"^name^"\n"
  ^"RS\t\t\t"^(string_of_spl rstep)^"\n"
  ^"COLD\t\t\t"^(String.concat ", " (List.map string_of_intexpr (IntExprSet.elements cold)))^"\n"
  ^"REINIT\t\t\t"^(String.concat ", " (List.map string_of_intexpr (IntExprSet.elements reinit)))^"\n"
  ^"HOT\t\t\t"^(String.concat ", " (List.map string_of_intexpr (IntExprSet.elements hot)))^"\n"
  ^(String.concat "" (List.map string_of_breakdown_enhanced breakdowns))^"\n"
  ^"\n"
;;

let string_of_lib (lib: lib) : string =
  String.concat "" (List.map string_of_rstep_partitioned lib)
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

let rec reconcile_constraints_on_spl ((constraints,spl) : (((intexpr * intexpr) list) * spl)) : spl =
  match constraints with
    (l,r) :: tl -> let f (e : intexpr) : intexpr = if (e=r) then l else e in
		   reconcile_constraints_on_spl ((List.map (fun (l,r) -> (f l, f r)) tl), ((meta_transform_intexpr_on_spl TopDown f) spl))
  | [] -> spl
;;

let rec reconcile_constraints_on_idxfunc ((constraints,idxfunc) : (((intexpr * intexpr) list) * idxfunc)) : idxfunc =
  match constraints with
    (l,r) :: tl -> let f (e : intexpr) : intexpr = if (e=r) then l else e in
		   reconcile_constraints_on_idxfunc ((List.map (fun (l,r) -> (f l, f r)) tl), ((meta_transform_intexpr_on_idxfunc TopDown f) idxfunc))
  | [] -> idxfunc
;;

let wrap_intexprs (count : int ref) (i : intexpr) : intexpr =
    match i with 
      IMul _ | IPlus _ | IDivPerfect _ | IFreedom _ | ILoopCounter _ | IArg _ -> 
	count := !count + 1;
	ICountWrap(!count, i)
    | x -> x  
;;

let wrap_intexprs_on_spl (e :spl) : spl =
  let count = ref 0 in
  (meta_transform_intexpr_on_spl TopDown (wrap_intexprs count)) e
;;

let wrap_intexprs_on_idxfunc (e :idxfunc) : idxfunc =
  let count = ref 0 in
  (meta_transform_intexpr_on_idxfunc TopDown (wrap_intexprs count)) e
;;

let unwrap_idxfunc (e:idxfunc) : idxfunc =
  let count = ref 0 in
  let h (e:idxfunc) : idxfunc = 
    match e with
      PreWrap(n,x,d)->
	count := !count + 1;
	Pre(FArg(("lambda"^(string_of_int !count)),d))
    | x -> x
  in
  (meta_transform_idxfunc_on_idxfunc TopDown h) e
;;

let unwrap_intexpr (e:intexpr) : intexpr = 
  match e with
    ICountWrap(l,r)->IArg l
  | x -> x
;;

let unwrap_spl (e:spl) : spl =
  (meta_transform_idxfunc_on_spl TopDown unwrap_idxfunc) ((meta_transform_intexpr_on_spl TopDown unwrap_intexpr) e)
;;

let replace_by_a_call_idxfunc (wrapped:idxfunc) (name:string) (unwrapped : idxfunc) : idxfunc = 
  let printer (args:intexpr IntMap.t) : string =
    String.concat ", " (List.map (fun ((i,e):int*intexpr) -> "( "^(string_of_int i)^ " = " ^(string_of_intexpr e)^")") (IntMap.bindings args));
  in
  let extractor (args:intexpr IntMap.t) : intexpr list =
    List.map (fun ((i,e):int*intexpr) -> e) (IntMap.bindings args)
  in
  let collect_binds (idxfunc:idxfunc) : intexpr list = 
    let binds (i : intexpr) : intexpr list =
      match i with
	ICountWrap _ -> [i]
      | _ -> []
    in
    ((meta_collect_intexpr_on_idxfunc binds) idxfunc) in
  let rec mapify (binds : intexpr list) (map : intexpr IntMap.t) : intexpr IntMap.t =
    match binds with
      [] -> map
    | ICountWrap(p,expr)::tl -> mapify tl (IntMap.add p expr map)
    | _ -> failwith "type is not supported"
  in
  let map = mapify (collect_binds wrapped) IntMap.empty in
  let args = extractor map in
  print_string ("WIP ok, so what do we have here?\nunwrapped: "^(string_of_idxfunc unwrapped)^"\nwrapped: "^(string_of_idxfunc wrapped)^"\nname: "^(name)^"\nmap: "^(printer map)^"\nnewcall: "^(String.concat ", " (List.map string_of_intexpr (extractor map)))^"\nnewdef: "^(string_of_idxfunc ((meta_transform_intexpr_on_idxfunc TopDown unwrap_intexpr) wrapped))^"\n\n"); (* FRED WAS HERE *)
  PreWrap(name, wrapped, (func_domain unwrapped)) 
;;

let wrap_precomputations (e :spl) : spl =
  let namemap = ref IdxFuncMap.empty in
  let count = ref 0 in
  let register_name (ffunc:idxfunc) : _ =
    count := !count + 1;
    let name = "FunctionalEnv"^(string_of_int !count) in
    namemap := IdxFuncMap.add ffunc name !namemap;
  in

  let ensure_name (ffunc:idxfunc) : string =
    if not(IdxFuncMap.mem ffunc !namemap) then (
      register_name ffunc;
    );
    IdxFuncMap.find ffunc !namemap
  in
  let transf (i : idxfunc) : idxfunc = 
    match i with 
      Pre f ->       
	let wrapped_expr = (wrap_intexprs_on_idxfunc f) in
	let func_constraints = (extract_constraints_func wrapped_expr) in
	let reconciled = reconcile_constraints_on_idxfunc (func_constraints,wrapped_expr) in
	let new_func = unwrap_idxfunc reconciled in
	let new_name = ensure_name new_func in
	replace_by_a_call_idxfunc reconciled new_name f 
    | x -> x
  in
  (meta_transform_idxfunc_on_spl TopDown transf) e  
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


let drop_RS : (spl -> spl) =
  let g (e : spl) : spl = 
    match e with
    | RS(x) -> x
    | x -> x
  in
  meta_transform_spl_on_spl BottomUp g
;;

let replace_by_a_call_spl ((wrapped,(name,unwrapped)) : (spl * (string * spl))) : spl =
  let collect_binds (spl:spl) : intexpr list = 
    let binds (i : intexpr) : intexpr list =
      match i with
	ICountWrap _ -> [i]
      | _ -> []
    in
    ((meta_collect_intexpr_on_spl binds) spl) in
  let rec mapify (binds : intexpr list) (map : intexpr IntMap.t) : intexpr IntMap.t =
    match binds with
      [] -> map
    | ICountWrap(p,expr)::tl -> mapify tl (IntMap.add p expr map)
    | _ -> failwith "type is not supported"
  in

  let fcollect_binds (spl:spl) : idxfunc list = 
    let binds (i : idxfunc) : idxfunc list =
      match i with
	PreWrap _ -> [i]
      | _ -> []
    in
    ((meta_collect_idxfunc_on_spl binds) spl) 
  in

  let res = UnpartitionnedCall(name, (mapify (collect_binds wrapped) IntMap.empty), (fcollect_binds wrapped), (range unwrapped), (domain unwrapped)) in 
  (* print_string ("WIP REPLACING:\nwrapped:"^(string_of_spl wrapped)^"\nunwrapped:"^(string_of_spl unwrapped)^"\nres:"^(string_of_spl res)^"\n\n"); *)
  res
;;

let collect_args (rstep : spl) : IntExprSet.t = 
  let args = ref  IntExprSet.empty in
  let g (e : intexpr) : _ =
    match e with
    | IArg _ -> args := IntExprSet.add e !args
    | _ -> ()
  in
  meta_iter_intexpr_on_spl g rstep;
  !args
;;


let compute_the_closure (stems : spl list) (algo : spl -> boolexpr * (intexpr*intexpr) list * spl) : closure = 
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
    print_string "LOOP\n";
    let rstep = List.hd !under_consideration in
    under_consideration := List.tl !under_consideration;
    print_string ("WIP RSTEP:\t\t"^(string_of_spl rstep)^"\n"); (* WIP *)
    let name = ensure_name rstep in
    let args = collect_args rstep in
    let (condition, freedoms, naive_desc) = algo rstep in
    let desc = apply_rewriting_rules (mark_RS(naive_desc)) in
    print_string ("WIP DESC:\t\t"^(string_of_spl desc)^"\n"); (* WIP *)
    let rses = collect_RS desc in


    let wrapped_precomps = List.map wrap_precomputations rses in
    print_string ("WIP DESC wrapped precomps:\n"^(String.concat ",\n" (List.map string_of_spl wrapped_precomps))^"\n\n"); (* WIP *)

    let wrapped_intexpr = List.map wrap_intexprs_on_spl wrapped_precomps in
    print_string ("WIP DESC wrapped intexprs:\n"^(String.concat ",\n" (List.map string_of_spl wrapped_intexpr))^"\n\n"); (* WIP *)


    let constraints = List.map extract_constraints_spl wrapped_intexpr in
    let wrapped_RSes = List.map reconcile_constraints_on_spl (List.combine constraints wrapped_intexpr) in


    (* let wrapped_RSes = List.map wrap_exprs rses in *)
    print_string ("WIP DESC wrapped:\n"^(String.concat ",\n" (List.map string_of_spl wrapped_RSes))^"\n\n"); (* WIP *)

    let new_steps = List.map unwrap_spl wrapped_RSes in
    print_string ("WIP DESC new steps:\n"^(String.concat ",\n" (List.map string_of_spl new_steps))^"\n\n"); (* WIP *)

    let new_names = List.map ensure_name new_steps in
    print_string ("WIP DESC newnames:\n"^(String.concat ",\n" (new_names))^"\n\n"); (* WIP *)

    let extracts_with_calls = List.map replace_by_a_call_spl (List.combine wrapped_RSes (List.combine new_names rses)) in
    print_string ("WIP DESC extracts_with_calls:\n"^(String.concat ",\n" (List.map string_of_spl extracts_with_calls))^"\n\n"); (* WIP *)

    let desc_with_calls = drop_RS (reintegrate_RS desc extracts_with_calls) in
    print_string ("WIP DESC with_calls:\n"^(string_of_spl desc_with_calls)^"\n\n"); (* WIP *)

    rsteps := !rsteps @ [(name, rstep, args, [(condition, freedoms, desc, desc_with_calls)])];
  done;
  !rsteps
;;

let dependency_map_of_closure (closure : closure) : SpecArgSet.t SpecArgMap.t =
  let depmap = ref SpecArgMap.empty in 
  let per_rstep ((name, _, _, breakdowns) : rstep_unpartitioned) : _=   
    let per_rule ((_,_,_,desc_with_calls):breakdown) : _ = 
      meta_iter_spl_on_spl ( function
      | UnpartitionnedCall(callee,vars,funcs,_,_) -> (*FIXME funcs not taken into account *)
	let g (arg:int) (expr:intexpr) : _ =
    	  let key = (callee,arg) in
    	  let h (e:intexpr): _ =
    	    match e with
    	      IArg i ->
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

let initial_hots_of_closure (closure: closure) : SpecArgSet.t =
  let hot_set = ref SpecArgSet.empty in
  let per_rstep ((name, _, _, breakdowns) : rstep_unpartitioned) : _=   
    let per_rule ((_,_,_,desc_with_calls):breakdown) : _ = 
      meta_iter_spl_on_spl ( function
      | UnpartitionnedCall(callee,vars,funcs,_,_) -> (*FIXME funcs not taken into account *)
	let g (arg:int) (expr:intexpr) : _ =
    	  let h (e:intexpr): _ =
    	    match e with
    	    | ILoopCounter _ -> hot_set := SpecArgSet.add (callee,arg) !hot_set 
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



let initial_colds_of_closure (closure: closure) : SpecArgSet.t =
  let cold_set = ref SpecArgSet.empty in

  let init_rstep ((name, rstep, args, breakdowns) : rstep_unpartitioned) : _=
    let add_args_to_cold (e:intexpr) : _ =
      match e with
	IArg i -> 
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
      res := IntExprSet.add (IArg i) !res
  in
  SpecArgSet.iter f s;
  !res
;;

let partition_map_of_closure (closure: closure) : (IntExprSet.t StringMap.t * IntExprSet.t StringMap.t * IntExprSet.t StringMap.t) = 
  let dependency_map = dependency_map_of_closure closure in
  let initial_colds = initial_colds_of_closure closure in
  let initial_hots = initial_hots_of_closure closure in
  let all_colds = backward_propagation initial_colds dependency_map in
  let all_hots = forward_propagation initial_hots dependency_map in

  let colds = ref StringMap.empty in
  let reinits = ref StringMap.empty in
  let hots = ref StringMap.empty in
  let partition_args ((name, rstep, args, breakdowns) : rstep_unpartitioned) : _=
    let necessarily_colds = filter_by_rstep name all_colds in
    let necessarily_hots = filter_by_rstep name all_hots in
    let not_constrained = IntExprSet.diff args (IntExprSet.union necessarily_colds necessarily_hots) in
    let reinit = IntExprSet.inter necessarily_colds necessarily_hots in
    reinits := StringMap.add name reinit !reinits;
    colds := StringMap.add name (IntExprSet.diff necessarily_colds reinit) !colds;
    hots := StringMap.add name (IntExprSet.diff (IntExprSet.union necessarily_hots not_constrained) reinit) !hots (* as hot as possible *)
  in
  List.iter partition_args closure;
  (!colds,!reinits,!hots)
;;

let lib_from_closure (closure: closure) : lib =
  let filter_by (args:intexpr IntMap.t) (set:IntExprSet.t) : intexpr list =
    List.map snd (List.filter (fun ((i,expr):int*intexpr) -> IntExprSet.mem (IArg i) set) (IntMap.bindings args))
  in
  let (cold,reinit,hot) = partition_map_of_closure closure in
  let f ((name, rstep, _, breakdowns) : rstep_unpartitioned) : rstep_partitioned =
    let g ((condition, freedoms, desc, desc_with_calls):breakdown) : breakdown_enhanced = 
      let childcount = ref 0 in
      let h (e:spl) : spl =
	match e with
	| UnpartitionnedCall (callee, args, funcs, range, domain) -> (*FIXME funcs not taken into account *)
	  childcount := !childcount + 1;
  	  PartitionnedCall(!childcount, callee, (filter_by args (StringMap.find callee cold)), (filter_by args (StringMap.find callee reinit)), (filter_by args (StringMap.find callee hot)), funcs (* (List.map snd (IntMap.bindings funcs)) *), range, domain)
	| x -> x
      in
      let partitioned = (meta_transform_spl_on_spl BottomUp h) desc_with_calls in
      let j (e:spl) : spl =
	match e with
	  ISum(_, _, PartitionnedCall(childcount, callee, cold, [], _,[],_,_)) -> Construct(childcount, callee, cold)
	| ISum(i, high, PartitionnedCall(childcount, callee, cold, reinit, _,funcs,_,_)) -> ISumReinitConstruct(childcount, i, high, callee, cold, reinit, funcs)
	| x -> x
      in
      let k (e:spl) : spl =
	match e with
	  PartitionnedCall(childcount, callee, _, [], hot, _, range, domain) -> Compute(childcount, callee, hot, range, domain)
	| ISum(i, high, PartitionnedCall(childcount, callee, _, _, hot,_,range, domain)) -> ISumReinitCompute(childcount, i, high, callee, hot, range, domain)
	| x -> x
      in
      (condition, freedoms, desc, partitioned, (meta_transform_spl_on_spl BottomUp j) partitioned, (meta_transform_spl_on_spl BottomUp k) partitioned) in
    (name, rstep, (StringMap.find name cold), (StringMap.find name reinit), (StringMap.find name hot), (List.map g breakdowns))
  in
  List.map f closure
;;

let make_lib (functionalities: spl list) (algo: spl -> boolexpr * (intexpr*intexpr) list * spl) : lib =
  let closure = compute_the_closure functionalities algo in
  lib_from_closure closure
;;

