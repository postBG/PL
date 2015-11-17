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

  (* TODO : Fill in the blank to complete this function *)
  let rec cps exp = 
    let var_list = collect_vars exp in
    let k = gen_var var_list in
    match exp with
    (* Base case expressions *)
    | Num n -> Fn (k, App (Var k, Num n))
    | Var x -> Fn (k, App (Var k, Var x))
    (* Expressions with one operand *)
    | Fst e -> Fn (k, App (cps e, (* Complete this *) todo))
    | Snd e -> Fn (k, App (cps e, (* Complete this *) todo))
    (* Expressions with two operands *)
    | Add (e1, e2) ->
      let v1 = gen_var var_list in
      let v2 = gen_var var_list in
      Fn (k, App (cps e1, Fn (v1, App (cps e2, Fn (v2, 
        App (Var k, Add (Var v1, Var v2))
      )))))
    | Sub (e1, e2) -> failwith "Unimplemented" (* TODO *)
    | And (e1, e2) -> failwith "Unimplemented" (* TODO *)
    | Pair (e1, e2) -> failwith "Unimplemented" (* TODO *)
    (* Expressions with three operands *)
    | Ifz (e1, e2, e3) -> Fn (k, App (cps e1, (* Complete this *) todo))
    (* Lambda term expressinos *)
    | Fn (x, e) -> Fn (k, App (Var k, (* Complete this *) todo))
    | Rec (f, x, e) -> Fn (k, App (Var k, (* Complete this *) todo))
    (* Function application *)
    | App (e1, e2) -> Fn (k, App (cps e1, (* Complete this *) todo))

end
