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

(* type program = exp
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
and var = string *)
(* 함수 호출 시 env를 그 때의 env로 가져옴.*)
let rec eval : Lang.exp -> env -> mem -> value * mem
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
| ISZERO(e1) ->
  let (n1, mem1) = eval e1 env mem in
    (match n1 with
    |Int n1 ->if n1=0 then (Bool true, mem1) else (Bool false, mem1)
    | _ -> raise (Failure "Type Error: non-numeric values")
    )
|IF(e1, e2, e3)->
  let (n1, mem1) = eval e1 env mem in
    (match n1 with
    |Bool n1 ->if n1 
      then eval e2 env mem1 
      else eval e3 env mem1
    | _ -> raise (Failure "Type Error: non-bool values")
    )(* and var = string *)
|LET(x, e1, e2) ->
  let (n1, mem1) = eval e1 env mem in
  let env1 = extend_env (x,n1) env in
  let (n2, mem2) = eval e2 env1 mem1 in
  (n2, mem2)
|LETREC(x1,x2,e1,e2) ->
  
|PROC(x, e1) -> (Procedure (x,e1), mem)
|CALL(e1, e2) ->(
  let (n1, mem1) = eval e1 env mem in
  let (n2, mem2) = eval e2 env mem1 in
  match n1 with
  |Procedure (x, e) -> 
    let env1 = extend_env (x, n2) env in
    let (n3, mem3) = eval e env1 mem2 in
    (n3, mem3)
  |_ -> raise (Failure "Type Error: non proc"))
|NEWREF(e1) ->
  let (n1, mem1) = eval e1 env mem in
  let newL = new_location() in
  let mem1 = extend_mem (newL, n1) mem in 
  (Loc newL, mem1) 
|SEQ(e1, e2) ->
  let (n1, mem1) = eval e1 env mem in 
  let (n2, mem2) = eval e2 env mem1 in
  (n2, mem2)
|BEGIN(e1) ->
  let (n1, mem1) = eval e1 env mem in
  (n1, mem1)
(* |CALL(e1, e2) ->
  let ((n1, e), mem1) = eval e1 env mem in
  let (n2, mem2) = eval e2 env mem1 in
  let env_2 = extend_env (n1,n2) env in
  let (n3, mem3) = eval e env_2 mem2 *)
(* |DEREF(e1) ->
  let (l, mem1) = eval e1 env mem

  |SETREF(e1)-> *)
(* |LETREC(x1, x2, e1, e2) ->
  let f = Procedure(x1, e1) in 
  let env1 = extend_env f env in
  let (n2, mem2) = eval e2 env1 mem in
    (match n1,n2 with
    |Int n1, Int n2 -> (Int n2,mem2)
    | _ -> raise (Failure "Type Error: non-numeric values")) 
|BEGIN(e1) -> (eval e1 env mem) *)
  (* and var = string *)

(* memory *)
(* let empty_mem = [] 
let extend_mem (l,v) m = (l,v)::m
let rec apply_mem m l = 
  match m with
  | [] -> raise (Failure ("Location " ^ string_of_int l ^ " is unbound in Mem"))
  | (y,v)::tl -> if l = y then v else apply_mem tl l

(* use the function 'new_location' to generate a fresh memory location *)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter *)

(* | LETREC of var * var * exp * exp
| LETMREC of var * var * exp * var * var * exp * exp  *)

(* var * var * exp * exp
  | READ
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


