(*
 * SNU 4190.310 Programming Languages 
 * Homework "Continuation Passing Style" Solution
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open M0.M0

module CPS :
sig
  val cps : mexp -> mexp
end =
struct
  
  let id = ref 0

  let rec gen_var_helper var_list = 
    let _ = id := !id + 1 in
    let var_to_try = "x_" ^ (string_of_int !id) in
    if not (List.mem var_to_try var_list) then
      var_to_try
    else
      gen_var_helper var_list

  let gen_var var_list = gen_var_helper var_list

  let rec collect_vars = function
    | Var x -> [x]
    | Num _ -> []
    | Fst e | Snd e -> collect_vars e
    | Add (e1, e2) | Sub (e1, e2) | And (e1,e2) | Pair (e1, e2) | App (e1, e2) ->
      collect_vars e1 @ collect_vars e2
    | Ifz (e1, e2, e3) -> collect_vars e1 @ collect_vars e2 @ collect_vars e3
    | Fn (x, e) -> x :: collect_vars e
    | Rec (f, x, e) -> f :: x :: collect_vars e

  (* Dummy variable to mark what you have to do *)
  let todo = Num 0 

  let rec y_combinator var_list =
    let f = gen_var var_list in
    let x = gen_var var_list in
    Fn (f, 
      App (
        Fn (x, 
          App (
            Var f,
            App (Var x, Var x)
          )),
          Fn (x, 
            App (
              Var f, 
              App (Var x, Var x)
          ))
      )
    )

 

  (* TODO : Fill in the blank to complete this function *)
  let rec cps exp = 
    let var_list = collect_vars exp in
    let k = gen_var var_list in
    match exp with
    (* Base case expressions *)
    | Num n -> Fn (k, App (Var k, Num n))
    | Var x -> Fn (k, App (Var k, Var x))
    (* Expressions with one operand *)
    | Fst e -> 
      let v  = gen_var var_list in
      Fn (k, App (cps e, (Fn (v, App (Var k, Fst (Var v))))))
    | Snd e -> 
      let v  = gen_var var_list in
      Fn (k, App (cps e, (Fn (v, App (Var k, Snd (Var v))))))
    (* Expressions with two operands *)
    | Add (e1, e2) ->
      let v1 = gen_var var_list in
      let v2 = gen_var var_list in
      Fn (k, App (cps e1, Fn (v1, App (cps e2, Fn (v2, 
        App (Var k, Add (Var v1, Var v2))
      )))))
    | Sub (e1, e2) -> 
      let v1 = gen_var var_list in
      let v2 = gen_var var_list in
      Fn (k, App (cps e1, Fn (v1, App (cps e2, Fn (v2, 
        App (Var k, Sub (Var v1, Var v2))
      )))))
    | And (e1, e2) -> 
      let v1 = gen_var var_list in
      let v2 = gen_var var_list in
      Fn (k, App (cps e1, Fn (v1, App (cps e2, Fn (v2, 
        App (Var k, And (Var v1, Var v2))
      )))))
    | Pair (e1, e2) -> 
      let v1 = gen_var var_list in
      let v2 = gen_var var_list in
      Fn (k, App (cps e1, Fn (v1, App (cps e2, Fn (v2, 
        App (Var k, Pair (Var v1, Var v2))
      )))))
    (* Expressions with three operands *)
    | Ifz (e1, e2, e3) -> 
      let v1 = gen_var var_list in
      let v2 = gen_var var_list in
      let v3 = gen_var var_list in
      Fn (k, App (cps e1, Fn (v1, App (cps e2, Fn (v2, 
        App (cps e3, Fn (v3, App (Var k, Ifz (Var v1, Var v2, Var v3))))
      )))))
    (* Lambda term expressinos *)
    | Fn (x, e) -> 
      let k' = gen_var var_list in
      Fn (k, App (Var k, Fn (x, Fn (k', App (cps e, Var k')))))
    | Rec (f, x, e) -> 
      let k' = gen_var var_list in 
      Fn (k, App (Var k, (* Complete this *) todo))
    (* Function application *)
    | App (e1, e2) -> 
      let v = gen_var var_list in
      let f = gen_var var_list in
      Fn (k, App (cps e1, Fn (f, App (cps e2, Fn (v, App(App(Var f, Var v), Var k))))))

end
