(*
 * SNU 4190.310 Programming Languages 
 * Homework "Rozetta" Skeleton code
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open Sm5
open Sonata.Sonata

module Rozetta = struct
  exception Error of string

	let dummy_arg = (Val (Z 0))
	(*let counter = ref 0
	let newsl() = counter := !counter - 1; (!counter, 0)

	let alloc_special_loc() =
		let s_loc = newsl() in
		(Val (L s_loc))*)

	let rec trans_value : Sm5.value -> value =
		fun sm5_value ->
			match sm5_value with
			| Sm5.Z n -> Z n
			| Sm5.B b -> B b
			| Sm5.Unit -> Unit
			| _ -> raise (Error "invisible variable")
			
	let prev = "#prev" 
	let tmp_store_prev_fun = "#tempbox"
	let store_prev_fun = "#box"

	(* when mode 1 -> need not return, mode 2 -> return *)
	(* key invariant: #prev -> loc (-1, -1) -> (#prev_arg, removed C, E) *)
	let rec inner_trans : Sm5.command -> int -> command =
		fun sm5_cmds mode ->
			match sm5_cmds with
			| (Sm5.PUSH obj)::tail -> 
					(PUSH (trans_obj obj))::(inner_trans tail mode)
			| (Sm5.POP)::tail -> (POP)::(inner_trans tail mode)
			| (Sm5.STORE)::tail -> (STORE)::(inner_trans tail mode)
			| (Sm5.LOAD)::tail -> (LOAD)::(inner_trans tail mode)
			| (Sm5.JTR (cmd1, cmd2))::tail ->
					let sonata_cmd1 = inner_trans cmd1 2 in
					let sonata_cmd2 = inner_trans cmd2 2 in
					(JTR (sonata_cmd1, sonata_cmd2))::(inner_trans tail mode)
			| (Sm5.MALLOC)::tail -> (MALLOC)::(inner_trans tail mode)
			| (Sm5.BOX z)::tail -> (BOX z)::(inner_trans tail mode)
			| (Sm5.UNBOX x)::tail -> (UNBOX x)::(inner_trans tail mode)
			| (Sm5.BIND x)::tail -> (BIND x)::(inner_trans tail mode)
			| (Sm5.UNBIND)::tail -> (UNBIND)::(inner_trans tail mode)
			| (Sm5.GET)::tail -> (GET)::(inner_trans tail mode)
			| (Sm5.PUT)::tail -> (PUT)::(inner_trans tail mode)
			| (Sm5.ADD)::tail -> (ADD)::(inner_trans tail mode)
			| (Sm5.SUB)::tail -> (SUB)::(inner_trans tail mode)
			| (Sm5.MUL)::tail -> (MUL)::(inner_trans tail mode)
			| (Sm5.DIV)::tail -> (DIV)::(inner_trans tail mode)
			| (Sm5.EQ)::tail ->	(EQ)::(inner_trans tail mode)
			| (Sm5.LESS)::tail -> (LESS)::(inner_trans tail mode)
			| (Sm5.NOT)::tail -> (NOT)::(inner_trans tail mode)
			| (Sm5.CALL)::tail -> 
					let set_up_rec_cmds = set_up_recursive tail in
					set_up_rec_cmds@[(CALL)]
			| [] -> 
					if (mode = 1) then
						(PUSH (Id store_prev_fun))::(LOAD)::
							(PUSH dummy_arg)::MALLOC::
								(CALL)::[]
					else []
	and trans_obj : Sm5.obj -> obj =
		fun sm5_obj ->
			match sm5_obj with
			| Sm5.Val v -> Val (trans_value v)
			| Sm5.Id str -> Id str
			| Sm5.Fn (str, cmds) -> Fn (str, (inner_trans cmds 1))
	and set_up_recursive : Sm5.command -> command = (* exchange box pointer *)	
		fun sm5_cmds ->	
			let store_prev_condition_cmds = store_prev_condition sm5_cmds in
			let store_prev_condition_func = Fn("#prev_arg", store_prev_condition_cmds) in

			(PUSH (Id store_prev_fun))::(LOAD)::(*<x, C', E>::S*)	
				(MALLOC)::(BIND tmp_store_prev_fun)::
					(PUSH (Id tmp_store_prev_fun))::(STORE)::(*"tmp" => loc => <x, C', E>*)
						(PUSH store_prev_condition_func)::
							(PUSH (Id store_prev_fun))::(STORE)::[]
	and store_prev_condition : Sm5.command -> command =
		fun sm5_cmds ->
			let stored_cmds = (inner_trans sm5_cmds 1) in 
			(PUSH (Id tmp_store_prev_fun))::(LOAD)::
				(PUSH (Id store_prev_fun))::(STORE)::(* recover box first *)
					(UNBIND)::(POP)::
						stored_cmds
	
			
	(* set #box for key invariant. #box is always in env 
		#box has [("#prev", caller)]*)
	(* where caller = (x, C, E) *)
  	let rec trans : Sm5.command -> command = 
  		fun command -> 
  			let end_fun = (Fn ("#prev_arg", [])) in
  			(*let special_loc = alloc_special_loc() in*)

  			(PUSH end_fun)::(*remain env intact*)
  					(MALLOC)::(BIND store_prev_fun)::(*"store_prev_fun" => loc => (caller)*)
  						(PUSH (Id store_prev_fun))::(STORE)::(inner_trans command 1)

end
