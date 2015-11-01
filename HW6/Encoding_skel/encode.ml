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

	  let rec not_of_bool =
	  	Lambda.Lam
	  	(
	  		"#b",
	  		Lambda.Lam
	  		(
	  			"#x",
	  			Lambda.Lam
	  			(
	  				"#y",
	  				Lambda.App
	  				(
	  					Lambda.Id "#b",
	  					Lambda.App
	  					(
	  						Lambda.Id "#y",
	  						Lambda.Id "#x"
	  					)
	  				)
	  			)
	  		)
	  	)

	  let rec and_of_bool =
	  	Lambda.Lam
	  	(
	  		"#b",
	  		Lambda.Lam
	  		(
	  			"#b'",
	  			Lambda.Lam
	  			(
	  				"#x",
	  				Lambda.Lam
	  				(
	  					"#y",
	  					Lambda.App
	  					(	
		  					Lambda.App
		  					(
		  						Lambda.Id "#b",
			  					Lambda.App
			  					(
			  						Lambda.App(
			  							Lambda.Id "#c",
			  							Lambda.Id "#x"
			  						),
			  						Lambda.Id "#y"
			  					)	
		  					),
		  					Lambda.Id "#y"
		  				)
	  				)
	  			)
	  		)
	  	)

	  let rec is_zero = 
	  	Lambda.Lam("#n", Lambda.Lam("#x", Lambda.Lam("#y", 
	  				Lambda.App(Lambda.App(Lambda.Id "#n",
	  					Lambda.Lam("#x", Lambda.Id "#y")),
	  					Lambda.Id "#x"
	  				))))


	  let rec add =
			Lambda.Lam("#n",Lambda.Lam("#n'",Lambda.Lam("#f",Lambda.Lam("#x",
				Lambda.App(Lambda.App(Lambda.Id "#n",Lambda.Id "#f"),
					Lambda.App(Lambda.App(Lambda.Id "#n'",Lambda.Id "#f"),
						Lambda.Id "#x"))))))
	
		let rec church_pair =
			Lambda.Lam("#x", Lambda.Lam("#y", Lambda.Lam("#z", 
				Lambda.App(Lambda.App(Lambda.Id "#z", Lambda.Id "#x"), 
					Lambda.Id "#y")
			)))

		let rec church_fst = 
			Lambda.Lam("#p", Lambda.App(Lambda.Id "#p", 
				Lambda.Lam("#x", Lambda.Lam("#y", Lambda.Id "#x"))
			))

		let rec church_snd =
			Lambda.Lam("#p", Lambda.App(Lambda.Id "#p",
				Lambda.Lam("#x", Lambda.Lam("#y", Lambda.Id "#y"))
			))

		let rec encode : M.mexp -> Lambda.lexp =
			fun pgm ->
				match pgm with 
				| Num n -> (make_num n)
				| Var str -> Lambda.Id str
				| Fn (x, e) -> Lambda.Lam (x, encode e)
				| App (e1, e2) -> Lambda.App (encode e1, encode e2)
				| Rec (f, x, e) -> raise (Error "not implemented")
				| Ifz (e1, e2, e3) -> 						
						Lambda.App(Lambda.App(Lambda.App(is_zero, encode e1),encode e2),encode e3)
				| Pair (e1, e2) -> 
						let encoded_e1 = encode e1 in
						let encoded_e2 = encode e2 in
						Lambda.App(Lambda.App(church_pair, encoded_e1), encoded_e2)
				| Fst e -> Lambda.App(church_fst, encode e) 
				| Snd e -> Lambda.App(church_snd, encode e) 
				| Add (e1, e2) -> 
						let encoded_e1 = encode e1 in
						let encoded_e2 = encode e2 in
						Lambda.App(Lambda.App(add, encoded_e1), encoded_e2) 
				| Sub (e1, e2) -> raise (Error "not implemented") 
				| And (e1, e2) -> raise (Error "not implemented")
				 

 end
