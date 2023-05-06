open Lang (* enable to use all stuff in lang.ml *)

type value = 
    Int of int 
  | Bool of bool 
  | Procedure of var * exp
  | Loc of loc
and loc = int
and env = (var * value) list
and mem = (loc * value) list

(* conversion of value to string *)
let value2str v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Loc l -> "Loc "^(string_of_int l)
  | Procedure (x,e) -> "Procedure "

(* environment *)
let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec apply_env e x = 
  match e with
  | [] -> raise (Failure (x ^ " is unbound in Env"))
  | (y,v)::tl -> if x = y then v else apply_env tl x

(* memory *)
let empty_mem = [] 
let extend_mem (l,v) m = (l,v)::m
let rec apply_mem m l = 
  match m with
  | [] -> raise (Failure ("Location " ^ string_of_int l ^ " is unbound in Mem"))
  | (y,v)::tl -> if l = y then v else apply_mem tl l

(* use the function 'new_location' to generate a fresh memory location *)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

(* represent the given environment as a string (use this for debugging) *)
let rec string_of_env env = 
	(List.fold_left (fun acc (x,v) -> Printf.sprintf "%s, %s |-> %s" acc x (value2str v)) "{" env) ^ "}" 

(* represent the given memory as a string (use this for debugging) *)
let rec string_of_mem mem = 
	(List.fold_left (fun acc (l,v) -> Printf.sprintf "%s, %d |-> %s" acc l (value2str v)) "{" mem) ^ "}" 
		 

(*****************************************************************)
(* TODO: Implement the eval function. Modify this function only. *)
(*****************************************************************)
(* let rec eval : exp -> env -> mem -> value * mem
=fun exp env mem -> raise NotImplemented *)

type program = exp
and exp =
| CONST of int
| VAR of var
| ADD of exp * exp
| SUB of exp * exp
| MUL of exp * exp
| DIV of exp * exp
| EQ of exp * exp
| LT of exp * exp
| ISZERO of exp
| READ
| IF of exp * exp * exp
| LET of var * exp * exp
| LETREC of var * var * exp * exp
| LETMREC of var * var * exp * var * var * exp * exp
| PROC of var * exp
| CALL of exp * exp
| NEWREF of exp
| DEREF of exp
| SETREF of exp * exp
| SEQ of exp * exp
| BEGIN of exp
and var = string
(* 함수 호출 시 env를 그 때의 env로 가져옴.*)
let rec eval : exp -> env -> mem -> value * mem
= fun exp env mem ->
  match exp with
| CONST n -> (Int n, mem)
| VAR x -> ((apply_env env x), mem)
| ADD(e1, e2) -> 
  let (n1, mem1) = eval e1 env mem in
  let (n2, mem2) = eval e2 env mem1 in
    (match n1,n2 with
    | Int n1, Int n2 -> (Int (n1 + n2),mem2)
    | _ -> raise (Failure "Type Error: non-numeric values")) 
| SUB(e1, e2) -> 
  let (n1, mem1) = eval e1 env mem in
  let (n2, mem2) = eval e2 env mem1 in
    (match n1,n2 with
    | Int n1, Int n2 -> (Int (n1 - n2),mem2)
    | _ -> raise (Failure "Type Error: non-numeric values")) 
| MUL(e1, e2) -> 
  let (n1, mem1) = eval e1 env mem in
  let (n2, mem2) = eval e2 env mem1 in
    (match n1,n2 with
    | Int n1, Int n2 -> (Int (n1 * n2),mem2)
    | _ -> raise (Failure "Type Error: non-numeric values")) 
| DIV (e1, e2)->
  let (n1, mem1) = eval e1 env mem in
  let (n2, mem2) = eval e2 env mem1 in
    (match n1,n2 with
    |Int n1, Int 0 -> raise(Failure "Divide By Zero")
    |Int n1, Int n2 ->(Int (n1 / n2),mem2)
    | _ -> raise (Failure "Type Error: non-numeric values")
    )
| EQ(e1, e2) ->
  let (n1, mem1) = eval e1 env mem in
  let (n2, mem2) = eval e2 env mem1 in
    (match n1,n2 with
    |Int n1, Int n2 ->if n1=n2 then (Bool true, mem2) else (Bool false, mem2)
    | _ -> raise (Failure "Type Error: non-numeric values")
    )
| LT(e1, e2) ->
  let (n1, mem1) = eval e1 env mem in
  let (n2, mem2) = eval e2 env mem1 in
    (match n1,n2 with
    |Int n1, Int n2 ->if n1>n2 then (Bool true, mem2) else (Bool false, mem2)
    | _ -> raise (Failure "Type Error: non-numeric values")
    )
(* and var = string *)

(*  
  | LT -> 
  | ISZERO -> 
  | READ
  | IF -> 
  | LET -> 
  | LETREC -> 
  | LETMREC -> 
  | PROC -> 
  | CALL -> 
  | NEWREF -> 
  | DEREF -> 
  | SETREF -> 
  | SEQ -> 
  | BEGIN ->  *)
	
(* driver code *)
let run : program -> value
=fun pgm -> (fun (v,_) -> v) (eval pgm empty_env empty_mem) 


