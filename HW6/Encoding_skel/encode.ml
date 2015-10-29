(*
 * SNU 4190.310 Programming Languages 
 *
 * M0
 *)
open M
module Encoder = 
  struct
  	exception Error of string

	  let rec inner_make_num : int -> Lambda.lexp =
	  	fun n ->
	  		if n < 0 then raise (Error "Negative exception")
	  		else if n = 0 then (Lambda.Id "#x")
	  		else
	  			let f_form = inner_make_num (n-1) in
	  			(Lambda.App (Lambda.Id "#f", f_form))


	  let rec make_num : int -> Lambda.lexp =
	  	fun n ->
	  		let f_form = inner_make_num n in
	  		Lambda.Lam ("#f", Lambda.Lam("#x", f_form))

	  let rec true_of_bool = Lambda.Lam ("#x", (Lambda.Lam ("#y", "#x")))

	  let rec false_of_bool = Lambda.Lam ("#x", (Lambda.Lam ("#y", "#y")))

		let encode : M.mexp -> Lambda.lexp =
			fun pgm -> 
				| Num n -> (make_num n) 
				| Var str -> raise (Error "not implemented") (* Implement this *)
				| Fn (x, e) -> raise (Error "not implemented") (* Implement this *)
				| App (e1, e2) -> raise (Error "not implemented") (* Implement this *)
				| Ifz (e1, e2, e3) -> raise (Error "not implemented") (* Implement this *)
				| Pair (e1, e2) -> raise (Error "not implemented") (* Implement this *)
				| Fst e -> raise (Error "not implemented") (* Implement this *)
				| Snd e -> raise (Error "not implemented") (* Implement this *)
				| Add (e1, e2) -> raise (Error "not implemented") (* Implement this *)
				| Sub (e1, e2) -> raise (Error "not implemented") (* Implement this *)
				| And (e1, e2) -> raise (Error "not implemented") (* Implement this *)
				| Rec (f, x, e) -> raise (Error "not implemented") (* Implement this *)

 end
