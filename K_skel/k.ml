(*
 * SNU 4190.310 Programming Languages 2015 Fall
 *  K- Interpreter Skeleton Code
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

(* Location Signature *)
module type LOC =
sig
  type t
  val base : t
  val equal : t -> t -> bool
  val diff : t -> t -> int
  val increase : t -> int -> t
end

module Loc : LOC =
struct
  type t = Location of int
  let base = Location(0)
  let equal (Location(a)) (Location(b)) = (a = b)
  let diff (Location(a)) (Location(b)) = a - b
  let increase (Location(base)) n = Location(base+n)
end

(* Memory Signature *)
module type MEM = 
sig
  type 'a t
  exception Not_allocated
  exception Not_initialized
  val empty : 'a t (* get empty memory *)
  val load : 'a t -> Loc.t  -> 'a (* load value : Mem.load mem loc => value *)
  val store : 'a t -> Loc.t -> 'a -> 'a t (* save value : Mem.store mem loc value => mem' *)
  val alloc : 'a t -> Loc.t * 'a t (* get fresh memory cell : Mem.alloc mem => (loc, mem') *)
end

(* Environment Signature *)
module type ENV =
sig
  type ('a, 'b) t
  exception Not_bound
  val empty : ('a, 'b) t (* get empty environment *)
  val lookup : ('a, 'b) t -> 'a -> 'b (* lookup environment : Env.lookup env key => content *)
  val bind : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t  (* id binding : Env.bind env key content => env'*)
end

(* Memory Implementation *)
module Mem : MEM =
struct
  exception Not_allocated
  exception Not_initialized
  type 'a content = V of 'a | U
  type 'a t = M of Loc.t * 'a content list
  let empty = M (Loc.base,[])

  let rec replace_nth = fun l n c -> 
    match l with
    | h::t -> if n = 1 then c :: t else h :: (replace_nth t (n - 1) c)
    | [] -> raise Not_allocated

  let load (M (boundary,storage)) loc =
    match (List.nth storage ((Loc.diff boundary loc) - 1)) with
    | V v -> v 
    | U -> raise Not_initialized

  let store (M (boundary,storage)) loc content =
    M (boundary, replace_nth storage (Loc.diff boundary loc) (V content))

  let alloc (M (boundary,storage)) = 
    (boundary, M (Loc.increase boundary 1, U :: storage))
end

(* Environment Implementation *)
module Env : ENV=
struct
  exception Not_bound
  type ('a, 'b) t = E of ('a -> 'b)
  let empty = E (fun x -> raise Not_bound)
  let lookup (E (env)) id = env id
  let bind (E (env)) id loc = E (fun x -> if x = id then loc else env x)
end

(*
 * K- Interpreter
 *)
module type KMINUS =
sig
  exception Error of string
  type id = string
  type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp            (* sequence *)
  | IF of exp * exp * exp       (* if-then-else *)
  | WHILE of exp * exp          (* while loop *)
  | LETV of id * exp * exp      (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list      (* call by value *)
  | CALLR of id * id list       (* call by referenece *)
  | RECORD of (id * exp) list   (* record construction *)
  | FIELD of exp * id           (* access record field *)
  | ASSIGN of id * exp          (* assgin to variable *)
  | ASSIGNF of exp * id * exp   (* assign to record field *)
  | READ of id
  | WRITE of exp
    
  type program = exp
  type memory
  type env
  type value =
  | Num of int
  | Bool of bool
  | Unit
  | Record of (id -> Loc.t)
  val emptyMemory : memory
  val emptyEnv : env
  val run : memory * env * program -> value
end

module K : KMINUS =
struct
  exception Error of string

  type id = string
  type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp            (* sequence *)
  | IF of exp * exp * exp       (* if-then-else *)
  | WHILE of exp * exp          (* while loop *)
  | LETV of id * exp * exp      (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list      (* call by value *)
  | CALLR of id * id list       (* call by referenece *)
  | RECORD of (id * exp) list   (* record construction *)
  | FIELD of exp * id           (* access record field *)
  | ASSIGN of id * exp          (* assgin to variable *)
  | ASSIGNF of exp * id * exp   (* assign to record field *)
  | READ of id
  | WRITE of exp

  type program = exp

  type value =
  | Num of int
  | Bool of bool
  | Unit
  | Record of (id -> Loc.t)
    
  type memory = value Mem.t
  type env = (id, env_entry) Env.t
  and  env_entry = Addr of Loc.t | Proc of id list * exp * env

  let emptyMemory = Mem.empty
  let emptyEnv = Env.empty

  let value_int v =
    match v with
    | Num n -> n
    | _ -> raise (Error "TypeError : not int")

  let value_bool v =
    match v with
    | Bool b -> b
    | _ -> raise (Error "TypeError : not bool")

  let value_unit v =
      match v with
      | Unit -> ()
      | _ -> raise (Error "TypeError : not unit")

  let value_record v =
      match v with
      | Record r -> r
      | _ -> raise (Error "TypeError : not record")

  let lookup_env_loc e x =
    try
      (match Env.lookup e x with
      | Addr l -> l
      | Proc _ -> raise (Error "TypeError : not addr")) 
    with Env.Not_bound -> raise (Error "Unbound")

  let lookup_env_proc e f =
    try
      (match Env.lookup e f with
      | Addr _ -> raise (Error "TypeError : not proc") 
      | Proc (id_list, exp, env) -> (id_list, exp, env))
    with Env.Not_bound -> raise (Error "Unbound")

  let rec set_env_mem : (id list * value list * memory * env) -> (memory * env) =
    fun (id_list, val_list, mem, env) ->
      match id_list, val_list with
      | [], [] -> (mem, env)
      | [], hd::tail -> raise (Error "InvalidArg")
      | hd::tail, [] -> raise (Error "InvalidArg")
      | i::id_tail, v::val_tail ->
        let (loc, mem') = Mem.alloc mem in
        let new_env = (Env.bind env i (Addr loc)) in
        let new_mem = (Mem.store mem' loc v) in
        set_env_mem(id_tail, val_tail, new_mem, new_env)

  let rec setting_env : (id list * id list * env) -> env =
    fun (x_list, y_list, env) ->
      match x_list, y_list with
      | [], [] -> env
      | [], hd::tail -> raise (Error "InvalidArg")
      | hd::tail, [] -> raise (Error "InvalidArg")
      | x::x_tail, y::y_tail ->
        let env' = (Env.bind env x (Addr (lookup_env_loc env y))) in
        setting_env(x_tail, y_tail, env')

  let rec alloc_loc_mem : (value list * memory) -> (Loc.t list * memory) =
    fun (val_list, mem) ->
      match val_list with
      | [] -> ([], mem)
      | v::val_tail ->
        let (loc, mem') = Mem.alloc mem in
        let new_mem = Mem.store mem' loc v in
        let (next_list, last_mem) = alloc_loc_mem(val_tail, new_mem) in
        (loc::next_list, last_mem)

  let rec find_list_entry(entry, lst, index) =
    match lst with
    | [] -> -1
    | hd::tail ->
      if hd = entry then index
      else find_list_entry(entry, tail, index + 1)

  let rec find_record_entry : (id * id list * Loc.t list) -> Loc.t =
    fun (id, id_list, loc_list) ->
      let index = find_list_entry(id, id_list, 0) in
      if index = -1 then raise (Error("Not in record"))
      else (List.nth loc_list index)

  let rec eval : memory -> env -> exp -> (value * memory) =
    fun mem env e ->
    match e with
    | NUM i -> (Num i, mem)
    | TRUE -> (Bool true, mem)
    | FALSE -> (Bool false, mem)
    | UNIT -> (Unit, mem)
    | VAR id -> (Mem.load mem (lookup_env_loc env id), mem)
    | ADD (exp1, exp2) -> 
      let (n1, mem') = eval mem env exp1 in 
      let (n2, mem'') = eval mem' env exp2 in
      let v1 = value_int n1 in
      let v2 = value_int n2 in
      let new_v = Num (v1 + v2) in
      (new_v, mem'')
    | SUB (exp1, exp2) ->
      let (n1, mem') = eval mem env exp1 in
      let (n2, mem'') = eval mem' env exp2 in
      let v1 = value_int n1 in
      let v2 = value_int n2 in
      let new_v = Num (v1 - v2) in
      (new_v, mem'')
    | MUL (exp1, exp2) ->
      let (n1, mem') = eval mem env exp1 in
      let (n2, mem'') = eval mem' env exp2 in
      let v1 = value_int n1 in
      let v2 = value_int n2 in
      let new_v = Num (v1 * v2) in
      (new_v, mem'')
    | DIV (exp1, exp2) ->
      let (n1, mem') = eval mem env exp1 in
      let (n2, mem'') = eval mem' env exp2 in
      let v1 = value_int n1 in
      let v2 = value_int n2 in
      let new_v = Num (v1 / v2) in
      (new_v, mem'')
    | EQUAL (exp1, exp2) ->
      let (n1, mem') = eval mem env exp1 in
      let (n2, mem'') = eval mem' env exp2 in
      if n1 = n2 then (Bool true, mem'')
      else (Bool false, mem'')
    | LESS (exp1, exp2) ->
      let (n1, mem') = eval mem env exp1 in
      let (n2, mem'') = eval mem' env exp2 in
      let v1 = value_int n1 in
      let v2 = value_int n2 in
      let new_v = Bool (v1 < v2) in
      (new_v, mem'')
    | NOT exp ->
      let (b1, mem') = eval mem env exp in
      let v1 = value_bool b1 in
      let new_v = Bool (not v1) in
      (new_v, mem')
    | SEQ (exp1, exp2) ->
      let (v1, mem') = eval mem env exp1 in
      let (v2, mem'') = eval mem' env exp2 in
      (v2, mem'')
    | IF (cond_exp, then_exp, else_exp) ->
      let (b, mem') = eval mem env cond_exp in
      if (value_bool b) then (eval mem' env then_exp)
      else (eval mem' env else_exp)
    | WHILE (cond_exp, body_exp) ->
      let (b, mem') = eval mem env cond_exp in
      if (value_bool b) 
      then 
        let (v1, mem1) = eval mem' env body_exp in
        eval mem1 env (WHILE (cond_exp, body_exp))
      else (Unit, mem') 
    | LETF (id, arg_list, exp1, exp2) ->
      let v = Proc (arg_list, exp1, env) in
      let new_env = (Env.bind env id v) in
      (eval mem new_env exp2)
    | CALLV (id, arg_list) ->
      let (val_list, mem_n) = make_value_list(arg_list, mem, env) in
      let (id_list, exp', env') = lookup_env_proc env id in
      let (set_mem, semi_set_env) = set_env_mem(id_list, val_list, mem_n, env') in
      let set_env = Env.bind semi_set_env id (Proc (id_list, exp', env')) in
      (eval set_mem set_env exp')
    | CALLR (id, arg_list) ->
      let (id_list, exp, env') = lookup_env_proc env id in
      let semi_set_env = setting_env(id_list, arg_list, env) in
      let set_env = Env.bind semi_set_env id (Proc (id_list, exp, env')) in
      (eval mem set_env exp)
    | RECORD idXexp_list ->
      (match idXexp_list with
      | [] -> (Unit, mem)
      | _ ->
        let (id_list, exp_list) = List.split idXexp_list in
        let (val_list, mem_n) = make_value_list(exp_list, mem, env) in
        let (loc_list, new_mem) = alloc_loc_mem(val_list, mem_n) in
        ( (Record (fun x -> find_record_entry(x, id_list, loc_list))), new_mem)
      )
    | FIELD (exp, id) ->
      let (r, mem') = eval mem env exp in
      (Mem.load mem' ((value_record r) id), mem')
    | ASSIGNF (exp1, id, exp2) ->
      let (r, mem1) = eval mem env exp1 in
      let (v, mem2) = eval mem1 env exp2 in
      (v, Mem.store mem2 ((value_record r) id) v)
    | READ x -> (*from here*)
      let v = Num (read_int()) in
      let l = lookup_env_loc env x in
      (v, Mem.store mem l v)
    | WRITE e ->
      let (v, mem') = eval mem env e in
      let n = value_int v in
      let _ = print_endline (string_of_int n) in
      (v, mem')
    | LETV (x, e1, e2) ->
      let (v, mem') = eval mem env e1 in
      let (l, mem'') = Mem.alloc mem' in
      eval (Mem.store mem'' l v) (Env.bind env x (Addr l)) e2
    | ASSIGN (x, e) ->
      let (v, mem') = eval mem env e in
      let l = lookup_env_loc env x in
      (v, Mem.store mem' l v)
    | _ -> failwith "Unimplemented" (* TODO : Implement rest of the cases *)
    and make_value_list : (exp list * memory * env) -> (value list * memory) =
    fun (exp_list, mem, env) ->
      match exp_list with
      | [] -> ([], mem)
      | hd::tail ->
        let (v, mem') = eval mem env hd in
        let (val_list, last_mem) = make_value_list(tail, mem', env) in
        (v::val_list, last_mem)

  let run (mem, env, pgm) = 
    let (v, _ ) = eval mem env pgm in
    v
end
