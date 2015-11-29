(*
 * SNU 4190.310 Programming Languages 
 * Homework "Exceptions are sugar" Skeleton
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open Xexp

exception Error of string

let count = ref 0

let new_name () = 
  let _ = count := !count + 1 in
  "x_" ^ (string_of_int !count)

let rec alpha_conv exp subs = 
  match exp with
  | Num n -> Num n
  | Var x -> (try Var (List.assoc x subs) with Not_found -> Var x)
  | Fn (x, e) ->
    let x' = new_name () in
    let subs' = (x, x') :: subs in
    Fn (x', alpha_conv e subs')
  | App (e1, e2) -> App (alpha_conv e1 subs, alpha_conv e2 subs)
  | If (e1, e2, e3) -> 
    If (alpha_conv e1 subs, alpha_conv e2 subs, alpha_conv e3 subs)
  | Equal (e1, e2) -> Equal (alpha_conv e1 subs, alpha_conv e2 subs)
  | Raise e -> Raise (alpha_conv e subs)
  | Handle (e1, n, e2) -> Handle (alpha_conv e1 subs, n, alpha_conv e2 subs)

let rec cps exp = 
  let k = new_name () in
  let h = new_name () in
  match exp with
  (* Constant expressions *)
  | Num n -> Fn (k, Fn (h, App(Var k, Num n)))
  | Var x -> Fn (k, Fn (h, App(Var k, Var x)))
  | Fn (x, e) -> 
  	let k' = new_name() in
  	let h' = new_name() in
  	Fn(k, Fn(h,
  		App(Var k, 
  			Fn(x, Fn(k', Fn(h', 
  			App(App(cps e, Var k'), Var h'))))
  		)
  	))
  (* Non constant expressions *)
  | App (e1, e2) ->
  	let f = new_name() in
  	let v = new_name() in
  	
  	let cps_e2 = cps e2 in
  	let k_of_cps_e2 = Fn(v, App(App(App(Var f, Var v), Var k), Var h)) in
  	let h_of_cps_e2 = Var h in
  	let normal_form_e2 = App(App(cps_e2, k_of_cps_e2), h_of_cps_e2) in

  	let cps_e1 = cps e1 in
  	let k_of_cps_e1 = Fn(f, normal_form_e2) in
  	let h_of_cps_e1 = Var h in
  	let normal_form_e1 = App(App(cps_e1, k_of_cps_e1), h_of_cps_e1) in
  
  	Fn(k, Fn(h, normal_form_e1))
  | If (e1, e2, e3) -> raise (Error "not implemented")
  | Equal (e1, e2) -> raise (Error "not implemented")
  | Raise e -> Fn(k, Fn(h, App(App(cps e, Var h), Var h)))
  | Handle (e1, n, e2) -> 
  	let except = Num n in
  	let x = new_name() in

  	let cps_e2 = cps e2 in
  	let k_of_cps_e2 = Var k in
  	let h_of_cps_e2 = Var h in
  	let normal_form_e2 = App(App(cps_e2, k_of_cps_e2), h_of_cps_e2) in

  	let cps_e1 = cps e1 in
  	let k_of_cps_e1 = Var k in
  	let prop_raise = cps (Raise (Var x)) in
  	let else_cps = App(App(prop_raise, Var k), Var h) in
  	let h_of_cps_e1 = Fn(x, If(Equal(Var x, except), normal_form_e2, else_cps)) in
  	let normal_form_e1 = App(App(cps_e1, k_of_cps_e1), h_of_cps_e1) in

  	Fn(k, Fn(h, normal_form_e1))

(* TODO : Implement this function *)
let removeExn : xexp -> xexp = 
	fun e ->
	  let x = new_name() in
	  let last_normal_conti = Fn (x, Var x) in

	  let magic_number = Num 201511 in
	  let last_exception_conti = Fn (x, magic_number) in
	  App(App(cps e, last_normal_conti), last_exception_conti)

