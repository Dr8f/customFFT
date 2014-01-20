open Lib
;;

type ctype = 
  Int
| Env of string
| Func
;;

type var = 
|Var of ctype * string
;;

type rvalue = 
  ContentsOf of var
| Equal of rvalue * rvalue
| IntexprValueOf of Spl.intexpr
| BoolValueOf of Spl.boolexpr
| IdxfuncValueOf of Spl.idxfunc
;;

type envrvalue = 
CreateEnv of string * rvalue list
;;

type envlvalue = 
  Into of var
| Nth of var * rvalue
;;

type code =
  Class of string(*name*) * var list(*cold args*) * var list(*reinit args*) * var list(*hot args*) * var list(*funcs*) * code (*cons*) * code (*comp*) * string (*output*) * string (*input*) * string list (*childX*) * var list (*freedoms*)
| FuncEnv of string(*name*) * var list(*args*) * var list(*funcs*) * code
| Chain of code list
| Noop
| Error of string
| Assign of var * rvalue 
| EnvAllocateConstruct of string * envrvalue
| EnvArrayAllocate of string * string * rvalue
| EnvArrayConstruct of envlvalue * envrvalue
| MethodCall of envlvalue * string * rvalue list * string * string
| If of rvalue * code * code
| Loop of var * rvalue * code
| BufferAllocate of string * rvalue
| BufferDeallocate of string * rvalue
| Return of int
;;

(* let meta_collect_code_on_code (f : code -> 'a list) : (code -> 'a list) = *)
(*   let z (g : code -> 'a list) (e : code) : 'a list = *)
(*     match e with *)
(*     | Class(_,_,_,_,cons,comp,_,_,_,_) -> (g cons) @ (g comp) *)
(*     | Chain l -> List.flatten (List.map g l) *)
(*     | If(_,a,b) -> (g a)@(g b) *)
(*     | Loop(_,_,c) -> g c *)
(*     | _ -> [] *)
(*   in *)
(*   Spl.recursion_collect f z *)
(* ;; *)

let collect_children ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) : string list =
  let res = ref [] in  
  let g ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : _ =
    Spl.meta_iter_spl_on_spl (function
    | Spl.Construct(numchild, _, _) -> res := ("child"^(string_of_int numchild))::!res
    | Spl.ISumReinitConstruct(numchild, i, count, rs, cold, reinit, funcs) -> res := ("child"^(string_of_int numchild))::!res
    | _ -> ()
    ) desc_cons;    
  in
  List.iter g breakdowns;
  !res
;;

let collect_freedoms ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) : var list =
  let res = ref [] in  
  let g ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : _ =
    res := (List.map (fun (l,r)->Var(Int,Spl.string_of_intexpr l)) freedoms) @ !res    
  in
  List.iter g breakdowns;
  !res  
;;

let cons_code_of_rstep_partitioned ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) : code =
  let prepare_env_cons (var:string) (rs:string) (args:Spl.intexpr list) : code =
    EnvAllocateConstruct (var, CreateEnv(rs, List.map (fun(x)->ContentsOf(Var(Int,Spl.string_of_intexpr x))) args))
  in

  let prepare_env_cons_loop (envlvalue:envlvalue) (rs:string) (args:Spl.intexpr list) (funcs:Spl.idxfunc list) : code = 
    EnvArrayConstruct (envlvalue, CreateEnv(rs, (List.map (fun(x)->ContentsOf(Var(Int,Spl.string_of_intexpr x))) args)@(List.map (fun(x)->IdxfuncValueOf x) funcs)))
  in

  let rec prepare_cons (e:Spl.spl) : code =
    match e with
    | Spl.Compose l -> Chain (List.map prepare_cons (List.rev l)) 
    | Spl.Construct(numchild, rs, cold) -> prepare_env_cons ("child"^(string_of_int numchild)) rs cold
    | Spl.ISumReinitConstruct(numchild, i, count, rs, cold, reinit, funcs) ->
      let name = "child"^(string_of_int numchild) in
      let loopvar = Var(Int, Spl.string_of_intexpr i) in 
      Chain([
	EnvArrayAllocate(name, rs, (IntexprValueOf count));
	Loop(loopvar, IntexprValueOf count, (prepare_env_cons_loop (Nth(Var(Env(rs), name), (ContentsOf(loopvar)))) rs (cold@reinit) funcs))  
      ])
    | _ -> Error("UNIMPLEMENTED")
  in
  let rulecount = ref 0 in
  let g (stmt:code) ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : code  =
    let freedom_assigns = List.map (fun (l,r)->Assign(Var(Int,Spl.string_of_intexpr l), ContentsOf(Var(Int,Spl.string_of_intexpr r)))) freedoms in
    rulecount := !rulecount + 1;
    
    If((BoolValueOf condition), 
       Chain( [Assign(Var(Int, "_rule"), IntexprValueOf(Spl.IConstant !rulecount))] @ freedom_assigns @ [prepare_cons desc_cons]), 
       Error("no applicable rules"))
      
  in
  List.fold_left g (Error("no error")) breakdowns
;;


let comp_code_of_rstep_partitioned ((name, rstep, cold, reinit, hot, funcs, breakdowns ) : rstep_partitioned) (output:string) (input:string): code =
  let prepare_env_comp (envlvalue:envlvalue) (rs:string) (args:Spl.intexpr list) (output:string) (input:string): code =
    MethodCall (envlvalue, "compute", (List.map (fun(x)->ContentsOf(Var(Int,Spl.string_of_intexpr x))) args), output, input)
  in

  let rec prepare_comp (output:string) (input:string) (e:Spl.spl): code =
    match e with
    | Spl.Compose l -> let buffernames = 
			 let count = ref 0 in
			 let g (res:string list) (_:Spl.spl) : string list = 
			   count := !count + 1; 
			   ("T"^(string_of_int !count)) :: res 
			 in
			 List.fold_left g [] (List.tl l) in
		       let out_in_spl = (List.combine (List.combine (buffernames @ [ output ]) (input :: buffernames)) (List.rev l)) in
		       let buffers = (List.combine (buffernames) (List.map Spl.range (List.rev (List.tl l)))) in
		       Chain (
			 (List.map (fun (output,size)->(BufferAllocate(output,IntexprValueOf(size)))) buffers)
			 @ (List.map (fun ((output,input),spl)->(prepare_comp output input spl)) out_in_spl)
			 @ (List.map (fun (output,size)->(BufferDeallocate(output,IntexprValueOf(size)))) buffers)
		       )
    | Spl.ISum(i, count, content) -> Loop(Var(Int, Spl.string_of_intexpr i), IntexprValueOf count, (prepare_comp output input content))
    | Spl.Compute(numchild, rs, hot,_,_) -> prepare_env_comp (Into(Var(Env(rs), "child"^(string_of_int numchild)))) rs hot output input
    | Spl.ISumReinitCompute(numchild, i, count, rs, hot,_,_) -> 
      let loopvar = Var(Int, Spl.string_of_intexpr i) in
      Loop(loopvar, IntexprValueOf count, (prepare_env_comp (Nth(Var(Env(rs), "child"^(string_of_int numchild)), (ContentsOf(loopvar)))) rs hot output input))
    | _ -> Error("UNIMPLEMENTED")
  in
  let rulecount = ref 0 in
  let g (stmt:code) ((condition,freedoms,desc,desc_with_calls,desc_cons,desc_comp):breakdown_enhanced) : code  =
    let freedom_assigns = List.map (fun (l,r)->Assign(Var(Int,Spl.string_of_intexpr l), ContentsOf(Var(Int,Spl.string_of_intexpr r)))) freedoms in
    rulecount := !rulecount + 1;
    
    If(Equal(ContentsOf(Var(Int, "_rule")), IntexprValueOf(Spl.IConstant !rulecount)),
       prepare_comp output input desc_comp, 
       Error("internal error: no valid rule has been selected"))
      
  in
  List.fold_left g (Error("no error")) breakdowns
;;



let code_of_lib ((funcs,rsteps) : lib) : code = 
  let code_of_func ((name, f, args, fargs) : envfunc) : code = 
    let count = ref 0 in
    let code_of_at (f : Spl.idxfunc) : code =
      let g (func:Spl.idxfunc) (code:code list): code list =
	count := !count + 1;
	code@[
	  match func with 
	  |Spl.FH(_,_,b,s) -> Assign(Var(Int,Spl.string_of_intexpr (Spl.ITmp(!count))), IntexprValueOf(Spl.IPlus([b;Spl.IMul([s;Spl.ITmp(!count-1)])])))
	  |Spl.FD(n,k) -> Assign(Var(Int,Spl.string_of_intexpr (Spl.ITmp(!count))), ContentsOf(Var(Int,"sp_omega("^(Spl.string_of_intexpr n)^", -(t"^(string_of_int (!count-1))^" % "^(Spl.string_of_intexpr k)^") * (t"^(string_of_int (!count-1))^ " / "^(Spl.string_of_intexpr k)^"))"))) (*FIXME horrendous piece of worthless code*)
	  |Spl.FArg(name,_) -> Assign(Var(Int,Spl.string_of_intexpr (Spl.ITmp(!count))), ContentsOf(Var(Int,name^"->at(t"^(string_of_int (!count-1))^")"))) (*FIXME ugliest code eva*)
	]
      in
      match f with
      |Spl.FCompose l -> Chain(List.fold_right g l [])
    in
    FuncEnv(name, 
	    List.map (function x -> Var(Int, Spl.string_of_intexpr x)) args,
	    List.map (function x -> Var(Func, Spl.string_of_idxfunc x)) fargs,
	    let code = (code_of_at f) in
	    Chain ( code :: [Return(!count)])
    )
  in
  let code_of_rstep (rstep_partitioned : rstep_partitioned) : code =
    let (name, rstep, cold, reinit, hot, funcs, breakdowns) = rstep_partitioned in 
    let output = "Y" in
    let input = "X" in
    Class (name,
	   List.map (function x -> Var(Int, Spl.string_of_intexpr x)) (IntExprSet.elements cold),
	   List.map (function x -> Var(Int, Spl.string_of_intexpr x)) (IntExprSet.elements reinit),
	   List.map (function x -> Var(Int, Spl.string_of_intexpr x)) (IntExprSet.elements hot),
	   List.map (function x -> Var(Func, Spl.string_of_idxfunc x)) funcs,
	   cons_code_of_rstep_partitioned rstep_partitioned,
	   comp_code_of_rstep_partitioned rstep_partitioned output input,
	   output,
	   input,
	   collect_children rstep_partitioned,
	   collect_freedoms rstep_partitioned
    )
  in
  Chain ((List.map code_of_func funcs)@(List.map code_of_rstep rsteps))
;;

