open Util
;;

(*********************************************
	 TYPES
*********************************************)

type ctype = 
  Int
| Env of string
| Func
| Ptr of ctype
| Char
| Complex
| Void
| Bool
;;

type expr = 
| Var of ctype * string
| Nth of expr * expr
| Cast of expr * ctype
| Equal of expr * expr
| New of expr
| Mul of expr * expr
| Plus of expr * expr
| Minus of expr * expr
| UniMinus of expr
| Mod of expr * expr
| Divide of expr * expr
| FunctionCall of string (*functionname*) * expr list (*arguments*)
| MethodCall of expr (*object*) * string (*method name*) * expr list (*arguments*)
| Const of int
| AddressOf of expr
;;

type cmethod = 
  Constructor of expr list(*args*) * code 
| Method of ctype (*return type*) * string (* functionname *) * expr list(* args*)  * code
and
code =
  Class of string(*class name*) * string (*class template from which it is derived*) * expr list (*member variables*) * cmethod list (*methods*)
| Chain of code list
| Noop
| Error of string
| Assign of expr(*dest*) * expr (*origin*)
| ArrayAllocate of expr (*pointer*) * ctype (*element type*) * expr (*element count*)
| PlacementNew of expr (*address*) * expr (*content*)
| If of expr (*condition*) * code (*true branch*) * code (*false branch*)
| Loop of expr (*loop variable*) * expr (*count*) * code 
| ArrayDeallocate of expr (*pointer*) * expr (*element count*)
| Return of expr
| Declare of expr
| Ignore of expr (*expression with side effect*)
;; 

(*********************************************
	 PRINTING
*********************************************)

let rec string_of_ctype (t : ctype) : string =
  match t with
  |Int -> "Int"
  |Func -> "Func"
  |Env(rs) -> "Env(\""^rs^"\")"
  |Ptr(ctype)->"Ptr("^(string_of_ctype ctype)^")"
  |Char -> "Char"
  |Complex -> "Complex"
  |Void -> "Void"
  |Bool -> "Bool"
;;

let rec string_of_expr (expr:expr) : string = 
  match expr with
  | Equal(a,b) -> "Equal(" ^ (string_of_expr a) ^ ", " ^ (string_of_expr b) ^ ")"
  | New(f) -> "New("^(string_of_expr f) ^")"
  | Nth(expr, count) ->"Nth("^(string_of_expr expr)^", "^(string_of_expr count)^")"
  | Var(a, b) -> "Var("^ (string_of_ctype a) ^ ", \"" ^ b ^ "\")"
  | Cast(expr, ctype) -> "Cast("^(string_of_expr expr)^", "^(string_of_ctype ctype)^")"
  | MethodCall(expr, methodname,args) -> "MethodCall("^(string_of_expr expr) ^ ", \""^methodname^"\", ["^(String.concat "; " (List.map string_of_expr args))^"])"
  | FunctionCall(functionname, args) -> "FunctionCall(\""^functionname^"\", ["^(String.concat "; " (List.map string_of_expr args))^"])"
  | Plus(a,b) -> "Plus("^(string_of_expr a)^", "^(string_of_expr b)^")"
  | Minus(a,b) -> "Minus("^(string_of_expr a)^", "^(string_of_expr b)^")"
  | Mul(a,b) -> "Mul("^(string_of_expr a)^", "^(string_of_expr b)^")"
  | Mod(a,b) -> "Mod("^(string_of_expr a)^", "^(string_of_expr b)^")"
  | Divide(a,b) -> "Divide("^(string_of_expr a)^", "^(string_of_expr b)^")"
  | UniMinus(a) -> "UniMinus("^(string_of_expr a)^")"
  | Const(a) -> "Const("^ (string_of_int a) ^")"
  | AddressOf(a) -> "AddressOf("^ (string_of_expr a) ^")"
;;

let rec string_of_code (n:int) (code : code) : string =
  (white n)^(
    match code with
      Chain l -> "Chain( [\n"^(String.concat ";\n" (List.map (string_of_code (n+4)) l))^"\n"^(white n)^"] )"
    | PlacementNew(l, r) -> "PlacementNew("^(string_of_expr l)^", "^(string_of_expr r)^")"
    | Assign(l, r) -> "Assign("^(string_of_expr l) ^ ", "^ (string_of_expr r) ^ ")"
    | Loop(var, expr, code) -> "Loop("^(string_of_expr var)^", "^(string_of_expr expr)^", \n"^(string_of_code  (n+4) code)^"\n"^(white n)^")"
    | ArrayAllocate(expr,elttype,int) -> "ArrayAllocate("^(string_of_expr expr)^", "^(string_of_ctype(elttype))^", "^(string_of_expr int)^")"
    | ArrayDeallocate(buf, size) -> "ArrayDeallocate("^(string_of_expr buf)^", "^(string_of_expr size)^")"
    | Return(expr) -> "Return("^(string_of_expr expr)^")"
    | Declare(expr) -> "Declare("^(string_of_expr expr)^")"
    | Noop -> "Noop"
   )   
;;

(*********************************************
	 METARULES                 
*********************************************)

let meta_transform_code_on_code (recursion_direction: recursion_direction) (f : code -> code) : (code -> code) =
  let z (g : code -> code) (e : code) : code = 
    match e with
    | Chain l -> Chain (List.map g l)
    | Loop(var, expr, code) -> Loop(var, expr, (g code))
    | PlacementNew _ | Assign _ | ArrayAllocate _ | ArrayDeallocate _ | Return _ | Declare _ | Noop _ -> e
  in
  recursion_transform recursion_direction f z
;;

let meta_collect_code_on_code (f : code -> 'a list) : (code -> 'a list) =
  let z (g : code -> 'a list) (e : code) : 'a list =
    match e with
      Chain l -> List.flatten (List.map g l)
    | Loop(_, _, code) -> g code
    | If(_, true_branch, false_branch) ->(g true_branch)@(g false_branch) 
    | _ -> []
  in
  recursion_collect f z
;;

let meta_collect_expr_on_expr (f : expr -> 'a list) : (expr -> 'a list) =
  let z (g : expr -> 'a list) (e : expr) : 'a list =
    match e with
      Nth(a,b) | Equal(a,b) | Mul(a,b) | Plus(a,b) | Minus(a,b) | Mod(a,b) | Divide(a,b) -> (g a)@(g b)
    | Cast(a,_) | New(a) | UniMinus(a) | AddressOf(a) -> g a
    | FunctionCall(_, l) -> List.flatten (List.map g l)
    | MethodCall(a, _, l) -> (g a)@(List.flatten (List.map g l))
    | _ -> []
  in
  recursion_collect f z
;;

let meta_collect_expr_on_code (f : expr -> 'a list) : (code -> 'a list) =
  let direct_from_code (ff : expr -> 'a list) (e : code) : 'a list =
    match e with
      Assign(dest, orig) -> (ff dest)@(ff orig)
    | ArrayAllocate (pointer, _, elcount) -> (ff pointer)@(ff elcount)
    | PlacementNew (address, content) -> (ff address)@(ff content)
    | If (condition, _, _) -> ff condition
    | Loop(var, expr, _) -> (ff var)@(ff expr)
    | ArrayDeallocate(pointer, elcount) -> (ff pointer)@(ff elcount)
    | Return(expr) | Declare(expr) | Ignore(expr) -> ff expr
    | Noop | Chain _ | Error _ -> []
    | Class (_, _, _, _) -> [] (* not seriously thought after*)
  in
  fun (e : code) ->
    let ff = meta_collect_expr_on_expr f in
    (meta_collect_code_on_code (direct_from_code ff )) e
;;

  
let meta_transform_expr_on_expr (recursion_direction: recursion_direction) (f : expr -> expr) : (expr -> expr) =
  let z (g : expr -> expr) (e : expr) : expr = 
    match e with
    | Equal(a,b) -> Equal(g a, g b)
    | Plus(a,b) -> Plus(g a, g b)
    | Minus(a,b) -> Minus(g a, g b)
    | Mul(a,b) -> Mul(g a, g b)
    | Cast(expr,ctype) -> Cast(g expr, ctype)
    | Nth(expr, count) -> Nth(g expr, g count)
    | Var _ | Const _ -> e
    | x -> failwith ("Pattern_matching failed:\n"^(string_of_expr x))
  in
  recursion_transform recursion_direction f z
;;

let meta_transform_expr_on_code (recursion_direction: recursion_direction) (f : expr -> expr) : (code -> code) =
  let g = meta_transform_expr_on_expr recursion_direction f in
  meta_transform_code_on_code recursion_direction ( function 
  | Declare e -> Declare (g e)
  | Assign(l, r) -> Assign(g l, g r)
  | Chain _ as x -> x
  | ArrayAllocate(a, ctype, b) -> ArrayAllocate(g a, ctype, g b)
  | ArrayDeallocate(a, b) -> ArrayDeallocate(g a, g b)
  | x -> failwith ("Pattern_matching failed:\n"^(string_of_code 0 x))
  )
;;

let expr_substitution_on_expr (target : expr) (replacement : expr) : (expr -> expr) =
  let g (e: expr) : expr = 
    if (e = target) then replacement else e
  in
  meta_transform_expr_on_expr TopDown g
;;

let expr_substitution_on_code (target : expr) (replacement : expr) : (code -> code) =
  let g (e: expr) : expr = 
    if (e = target) then replacement else e
  in
  meta_transform_expr_on_code TopDown g
;;

let gen_var =
object 
  val tbl = ref StringMap.empty;
  method get (ctype:ctype) (prefix:string) : expr =
    let count = if (StringMap.mem prefix !tbl) then (StringMap.find prefix !tbl)+1 else 1 in
    tbl := StringMap.add prefix count !tbl;
    Var(ctype, prefix^(string_of_int count))
end
;;
    


module StringMap = Map.Make(String)
;;

module IntMap = Map.Make(struct type t = int let compare = compare end)
;;

