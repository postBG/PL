(*
 * SNU 4190.310 Programming Languages (Fall 2014)
 *
 * SM5
 *)
open K
open Sm5
module Translator = struct


(* 1. calculated value will top of the stack *)
(* this function get pgm and previous cmds and make new cmds *)
let rec inner_trans : K.program -> Sm5.command -> Sm5.command =
	fun pgm cmds ->
		match pgm with
		| K.NUM n -> Sm5.PUSH (Sm5.Val (Sm5.Z n))::cmds
		| K.TRUE -> Sm5.PUSH (Sm5.Val (Sm5.B true))::cmds
		| K.FALSE -> Sm5.PUSH (Sm5.Val (Sm5.B false))::cmds
		| K.UNIT -> Sm5.PUSH (Sm5.Val Sm5.Unit)::cmds
		| K.VAR id -> Sm5.LOAD::(Sm5.PUSH (Sm5.Id id))::cmds
		| K.ADD (e1, e2) ->
			let e1_cmds = inner_trans e1 cmds in
			let e2_cmds = inner_trans e2 e1_cmds in
			Sm5.ADD::e2_cmds
		| K.SUB (e1, e2) ->
			let e1_cmds = inner_trans e1 cmds in
			let e2_cmds = inner_trans e2 e1_cmds in
			Sm5.SUB::e2_cmds
		| K.MUL (e1, e2) ->
			let e1_cmds = inner_trans e1 cmds in
			let e2_cmds = inner_trans e2 e1_cmds in
			Sm5.MUL::e2_cmds
		| K.DIV (e1, e2)->
			let e1_cmds = inner_trans e1 cmds in
			let e2_cmds = inner_trans e2 e1_cmds in
			Sm5.DIV::e2_cmds
		| K.EQUAL (e1, e2) ->
			let e1_cmds = inner_trans e1 cmds in
			let e2_cmds = inner_trans e2 e1_cmds in
			Sm5.EQ::e2_cmds
		| K.LESS (e1, e2) ->
			let e1_cmds = inner_trans e1 cmds in
			let e2_cmds = inner_trans e2 e1_cmds in
			Sm5.LESS::e2_cmds
		| K.NOT e ->
			let e_cmds = inner_trans e cmds in
			Sm5.NOT::e_cmds
		| K.ASSIGN (id, e) ->
			let e_cmds = inner_trans e cmds in
			let new_env_cmds = Sm5.STORE::(Sm5.PUSH (Sm5.Id id))::e_cmds in
			Sm5.LOAD::(Sm5.PUSH (Sm5.Id id))::new_env_cmds
		| K.IF (cond, e1, e2) ->
			let cond_cmds = inner_trans cond cmds in
			let comp_then_cmds = List.rev (inner_trans e1 []) in
			let comp_else_cmds = List.rev (inner_trans e2 []) in
			(Sm5.JTR (comp_then_cmds, comp_else_cmds))::cond_cmds
		| K.SEQ (e1, e2) ->
			let e1_cmds = inner_trans e1 cmds in
			inner_trans e2 e1_cmds(* Here *)
		| K.LETV (id, e1, e2) ->
			let e1_cmds = inner_trans e1 cmds in
			let bind_cmds = (Sm5.BIND id)::Sm5.MALLOC::e1_cmds in
			let store_cmds = (Sm5.STORE)::(Sm5.PUSH (Sm5.Id id))::bind_cmds in
			let e2_cmds = inner_trans e2 store_cmds in
			(* when end of use, remove this bind *)
			Sm5.POP::Sm5.UNBIND::e2_cmds
		| K.WRITE e ->
			let e_cmds = inner_trans e cmds in
			let store_tmp_cmds = Sm5.STORE::(Sm5.PUSH (Sm5.Id "#tmp"))::(Sm5.BIND "#tmp")::Sm5.MALLOC::e_cmds in
			let stack_value_twice_cmds = Sm5.LOAD::(Sm5.PUSH (Sm5.Id "#tmp"))::Sm5.LOAD::(Sm5.PUSH (Sm5.Id "#tmp"))::store_tmp_cmds in
			Sm5.POP::Sm5.UNBIND::Sm5.PUT::stack_value_twice_cmds
		| _ -> cmds


let rec trans : K.program -> Sm5.command = 
	fun pgm -> List.rev (inner_trans pgm [])

end
