(*
 * SNU 4190.310 Programming Languages 
 *
 * Sonata
 *)
open Sm5
open Sonata
module Rozetta = struct

	exception Error of string

	let special_loc = (Sonata.Val (Sonata.L (-1, -1)))
	let dummy_arg = (Sonata.Val (Sonata.Z 0))
	let dummy_arg_loc = (Sonata.Val (Sonata.L (-2, -2)))

	let rec trans_value : Sm5.value -> Sonata.value =
		fun sm5_value ->
			match sm5_value with
			| Sm5.Z n -> Sonata.Z n
			| Sm5.B b -> Sonata.B b
			| Sm5.Unit -> Sonata.Unit
			| _ -> raise (Error "why compile error")
			

	(* when mode 1 -> need not return, mode 2 -> return *)
	(* key invariant: #prev -> loc (-1, -1) -> (#prev_arg, removed C, E) *)
	let rec inner_trans : Sm5.command -> int -> Sonata.command =
		fun sm5_cmds mode ->
			match sm5_cmds with
			| (Sm5.PUSH obj)::tail -> 
					(Sonata.PUSH (trans_obj obj))::(inner_trans tail mode)
			| (Sm5.POP)::tail -> (Sonata.POP)::(inner_trans tail mode)
			| (Sm5.STORE)::tail -> (Sonata.STORE)::(inner_trans tail mode)
			| (Sm5.LOAD)::tail -> (Sonata.LOAD)::(inner_trans tail mode)
			| (Sm5.JTR (cmd1, cmd2))::tail ->
					let sonata_cmd1 = inner_trans cmd1 2 in
					let sonata_cmd2 = inner_trans cmd2 2 in
					(Sonata.JTR (sonata_cmd1, sonata_cmd2))::(inner_trans tail mode)
			| (Sm5.MALLOC)::tail -> (Sonata.MALLOC)::(inner_trans tail mode)
			| (Sm5.BOX z)::tail -> (Sonata.BOX z)::(inner_trans tail mode)
			| (Sm5.UNBOX x)::tail -> (Sonata.UNBOX x)::(inner_trans tail mode)
			| (Sm5.BIND x)::tail -> (Sonata.BIND x)::(inner_trans tail mode)
			| (Sm5.UNBIND)::tail -> (Sonata.UNBIND)::(inner_trans tail mode)
			| (Sm5.GET)::tail -> (Sonata.GET)::(inner_trans tail mode)
			| (Sm5.PUT)::tail -> (Sonata.PUT)::(inner_trans tail mode)
			| (Sm5.ADD)::tail -> (Sonata.ADD)::(inner_trans tail mode)
			| (Sm5.SUB)::tail -> (Sonata.SUB)::(inner_trans tail mode)
			| (Sm5.MUL)::tail -> (Sonata.MUL)::(inner_trans tail mode)
			| (Sm5.DIV)::tail -> (Sonata.DIV)::(inner_trans tail mode)
			| (Sm5.EQ)::tail ->	(Sonata.EQ)::(inner_trans tail mode)
			| (Sm5.LESS)::tail ->	(Sonata.LESS)::(inner_trans tail mode)
			| (Sm5.NOT)::tail -> (Sonata.NOT)::(inner_trans tail mode)
			| (Sm5.CALL)::tail -> raise (Error "not implemented")
			| [] -> 
				if (mode = 1) then
					(Sonata.PUSH (Sonata.Id "#prev"))::(Sonata.LOAD)::
						(Sonata.PUSH dummy_arg)::(Sonata.PUSH dummy_arg_loc)::
							(Sonata.CALL)::[]
				else []

	and trans_obj : Sm5.obj -> Sonata.obj =
		fun sm5_obj ->
			match sm5_obj with
			| Sm5.Val v -> Sonata.Val (trans_value v)
			| Sm5.Id str -> Sonata.Id str
			| Sm5.Fn (str, cmds) -> Sonata.Fn (str, (inner_trans cmds 1))

  let rec trans : Sm5.command -> Sonata.command = 
  	fun command -> (* set #prev for key invariant. #prev is always in env *)
  		let end_fun = (Sonata.Fn ("#prev_arg", [])) in

  		(Sonata.PUSH special_loc)::(Sonata.BIND "#prev")::
  			(Sonata.PUSH end_fun)::(Sonata.PUSH (Sonata.Id "prev"))::(Sonata.STORE)::
  				(inner_trans command 1)




end
