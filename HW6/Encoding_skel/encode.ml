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

	  let rec true_of_bool = Lambda.Lam ("#x", (Lambda.Lam ("#y", Lambda.Id "#x")))

	  let rec false_of_bool = Lambda.Lam ("#x", (Lambda.Lam ("#y", Lambda.Id "#y")))

		let rec encode : M.mexp -> Lambda.lexp =
			fun pgm ->
				match pgm with 
				| Num n -> (make_num n)
				| Var str -> Lambda.Id str
				| Fn (x, e) -> Lambda.Lam (x, encode e)
				| App (e1, e2) -> Lambda.App (encode e1, encode e2)
				| Rec (f, x, e) -> raise (Error "not implemented")
				| Ifz (e1, e2, e3) -> raise (Error "not implemented") 
				| Pair (e1, e2) -> raise (Error "not implemented") 
				| Fst e -> raise (Error "not implemented") 
				| Snd e -> raise (Error "not implemented") 
				| Add (e1, e2) -> raise (Error "not implemented") 
				| Sub (e1, e2) -> raise (Error "not implemented") 
				| And (e1, e2) -> raise (Error "not implemented") 
				 

 end
