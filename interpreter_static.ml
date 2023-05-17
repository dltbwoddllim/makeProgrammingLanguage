open Lang (* enable to use all stuff in lang.ml *)

type value = 
    Int of int 
  | Bool of bool 
  | Procedure of var * exp * env 
  | RecProcedure of var * var * exp * env
	| MRecProcedure of var * var * exp * var * var * exp * env
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
  | Procedure (x,e,env) -> "Procedure "
  | RecProcedure (f,x,e,env) -> "RecProcedure "^f
	| MRecProcedure (f,x,e1,g,y,e2,env) -> "MRecProcedure " ^ f ^ " and " ^ g 

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

let rec string_of_env env = 
    (List.fold_left (fun acc (x,v) -> Printf.sprintf "%s, %s |-> %s" acc x (value2str v)) "{" env) ^ "}" 
  
(* use the function 'new_location' to generate a fresh memory location *)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

(*****************************************************************)
(* TODO: Implement the eval function. Modify this function only. *)
(*****************************************************************)
let rec eval : Lang.exp -> env -> mem -> value * mem
=fun exp env mem ->
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
      |Int n1, Int n2 ->if n1<n2 then (Bool true, mem2) else (Bool false, mem2)
      | _ -> raise (Failure "Type Error: non-numeric values")
      )
  | ISZERO(e1) ->
    let (n1, mem1) = eval e1 env mem in
      (match n1 with
      |Int n1 ->if n1=0 then (Bool true, mem1) else (Bool false, mem1)
      | _ -> raise (Failure "Type Error: non-numeric values")
      )  
  | READ -> Int (read_int ()), mem
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
  |LETREC(f,x,e1,e2) ->(
    let env1 = extend_env (f,RecProcedure (f, x, e1,env)) env in
    let (n1, mem1) = eval e2 env1 mem in
    (n1, mem1))
  |LETMREC(f,x,e1,g,x2,e2,e3)->
    let env1 = extend_env (f,MRecProcedure (f, x, e1, g, x2, e2, env)) env in
    let (n1, mem1) = eval e3 env1 mem in
    (n1, mem1)
  |PROC(x, e1) -> (Procedure (x,e1,env), mem)
  |CALL(e1, e2) ->(
    let (n1, mem1) = eval e1 env mem in
    let (n2, mem2) = eval e2 env mem1 in
    match n1 with
    |Procedure (x, e, env) -> 
      let env1 = extend_env (x, n2) env in
      let (n3, mem3) = eval e env1 mem2 in
      (n3, mem3)
    | RecProcedure (f, x, e, env) ->
      let env2 = extend_env (f, RecProcedure (f, x, e, env)) env in
      let env3 = extend_env (x, n2) env2 in
      let (n3, mem3) = eval e env3 mem2 in
      (n3, mem3)
    | MRecProcedure (f, x, e1, g, x2, e2, env) ->
      let env2 = extend_env (f, MRecProcedure(f, x, e1, g, x2, e2, env)) env in
      let env3 = extend_env (g, MRecProcedure(f, x, e1, g, x2, e2, env)) env2 in
      let env4 = extend_env (x, n2) env3 in
      let (n3, mem3) = eval e2 env4 mem2 in
      (n3, mem3)
    |_ -> raise (Failure "Type Error: non proc"))
  |NEWREF(e1) ->
    let (n1, mem1) = eval e1 env mem in
    let newL = new_location() in
    let mem1 = extend_mem (newL, n1) mem in 
    (Loc newL, mem1) 
  |DEREF(e1) ->
    (let (l1, mem1) = eval e1 env mem in
    match l1 with
    |Loc l1 -> 
      let v = apply_mem mem1 l1 in
      (v, mem1)
    | _ -> raise (Failure "Type Error: non-Loc values"))
  |SETREF(e1, e2)->
    (let (l1, mem1) = eval e1 env mem in
    let (n1, mem2) = eval e2 env mem1 in
    match l1 with
    |Loc l1 -> 
      let mem3 = extend_mem (l1, n1) mem2 in
      (n1, mem3)
    | _ -> raise (Failure "Type Error: non-Loc values"))
  |SEQ(e1, e2) ->
    let (n1, mem1) = eval e1 env mem in 
    let (n2, mem2) = eval e2 env mem1 in
    (n2, mem2)
  |BEGIN(e1) ->
    let (n1, mem1) = eval e1 env mem in
    (n1, mem1)
  |_ -> raise (UndefinedSemantics)
    
(* driver code *)
let run : program -> value
=fun pgm -> (fun (v,_) -> v) (eval pgm empty_env empty_mem) 
