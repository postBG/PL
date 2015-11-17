(*
 * SNU 4190.310 Programming Languages 
 * M0 Language Interpreter
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

module M0 : sig
  type mexp = 
    | Num of int
    | Var of id
    | Fn of id * mexp
    | App of mexp * mexp
    | Rec of id * id * mexp
    | Ifz of mexp * mexp * mexp
    | Add of mexp * mexp
    | Sub of mexp * mexp
    | And of mexp * mexp
    | Pair of mexp * mexp      (* (e, e) *)
    | Fst of mexp            (*   e.1  *)
    | Snd of mexp            (*   e.2  *)
  and id = string

  type closure
  type value = 
    | N of int
    | P of value * value
    | C of closure

  val run : mexp -> value 
end = 
struct
  type mexp = 
    | Num of int
    | Var of id
    | Fn of id * mexp
    | App of mexp * mexp
    | Rec of id * id * mexp
    | Ifz of mexp * mexp * mexp
    | Add of mexp * mexp
    | Sub of mexp * mexp
    | And of mexp * mexp
    | Pair of mexp * mexp      (* (e, e) *)
    | Fst of mexp            (*   e.1  *)
    | Snd of mexp            (*   e.2  *)
  and id = string

  type value = 
    | N of int
    | P of value * value
    | C of closure
  and closure = fexpr * env
  and fexpr = Fun of id * mexp | RecFun of id * id * mexp
  and env = id -> value

  exception RunError of string
  exception TypeError of string

  let bind e x v = (fun y -> if y = x then v else e y)
    
  let getNum = function 
    | N n -> n 
    | _ -> raise (TypeError "not an int")

  let getPair = function 
    | (P (a,b)) -> (a, b) 
    | _ -> raise (TypeError "not a pair")

  let getClosure = function 
    | (C c) -> c 
    | _ -> raise (TypeError "not a function")

  let rec eval env exp = 
    match exp with
    | Num n -> N n
    | Var x -> env x
    | Fn (x, e) -> C (Fun (x, e), env)
    | Rec (f, x, e) -> C (RecFun (f, x, e), env)
    | App (e1, e2) ->
      let v2 = eval env e2 in
      let v1 = eval env e1 in
      let (c, env') = getClosure v1 in
      (match c with 
      | Fun (x, e) -> eval (bind env' x v2) e
      | RecFun (f, x, e) ->  
        let env'' = bind env' x v2 in
        let env''' = bind env'' f v1 in
        eval env''' e)
    | Ifz (e1, e2, e3) ->
      let v1 = eval env e1 in
      if getNum v1 = 0 then eval env e2 else eval env e3
    | Add (e1, e2) -> 
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      N (getNum v1 + getNum v2)
    | Sub (e1, e2) -> 
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      N (getNum v1 - getNum v2)
    | And (e1, e2) -> 
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      if getNum v1 = 0 then
        N 0
      else if getNum v2 = 0 then
        N 0
      else
        N 1
    | Pair (e1, e2) -> 
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      P (v1, v2)
    | Fst e -> 
      let v = eval env e in
      fst (getPair v)
    | Snd e -> 
      let v = eval env e in
      snd (getPair v)

  let emptyEnv = (fun x -> raise (RunError ("unbound id: " ^ x)))
  
  let run : mexp -> value = fun exp -> eval emptyEnv exp

end
