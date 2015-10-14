(*
 * SNU 4190.310 Programming Languages (Fall 2014)
 *
 * SM5
 *)
open K
open Sm5
module Translator = struct


let rec while_to_rec_fun : K.program -> K.program -> K.program =
	fun cond body ->
		K.LETF("rec_fun_while","cond_var",
		  K.IF(K.VAR("cond_var"),
		    K.SEQ(body, K.CALLV("rec_fun_while", cond)),(* then statement *)
		    K.UNIT (* else statement *)
		  ),
		  K.CALLV("rec_fun_while",cond) (* first call *)
		)

let rec for_to_while : K.id -> K.program -> K.program -> K.program -> K.program =
	fun id init_stat bound_stat body ->
		let inner_id = "#inner"^id in
		K.LETV(id, init_stat,
			K.LETV(inner_id, init_stat,
    			K.WHILE(K.LESS(K.VAR(id), K.ADD(bound_stat, K.NUM(1))),
      				K.SEQ(K.SEQ(body,
          					K.ASSIGN(inner_id, K.ADD(K.VAR(inner_id), K.NUM(1)))),
        				K.ASSIGN(id, K.VAR(inner_id)))
   	 			)
  			)
		)


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
		| K.WHILE (e1, e2) ->
			let k_minus_while = while_to_rec_fun e1 e2 in
			let while_cmds = inner_trans k_minus_while cmds in
			while_cmds
		| K.FOR (id, e1, e2, e3) ->
			let k_minus_while = for_to_while id e1 e2 e3 in
			let for_cmds = inner_trans k_minus_while cmds in
			for_cmds
		| K.SEQ (e1, e2) ->
			let e1_cmds = inner_trans e1 cmds in
			(* remove e1_cmds final value, according to semantics *)
			inner_trans e2 (Sm5.POP::e1_cmds)
		| K.LETV (id, e1, e2) ->
			let e1_cmds = inner_trans e1 cmds in
			let bind_cmds = (Sm5.BIND id)::Sm5.MALLOC::e1_cmds in
			let store_cmds = (Sm5.STORE)::(Sm5.PUSH (Sm5.Id id))::bind_cmds in
			let e2_cmds = inner_trans e2 store_cmds in
			(* when end of use, remove this bind *)
			Sm5.POP::Sm5.UNBIND::e2_cmds
		| K.LETF (id, arg, e1, e2) -> (* Here *)
			(* We want E'(after Sm5.CALL) has "id -> (arg, C', E')" 
			 * then C' must have bind id *)		
			let e1_cmds = inner_trans e1 [] in
			let body = List.rev e1_cmds in
			let bind_function_cmds = (Sm5.BIND id)::(Sm5.PUSH (Sm5.Fn (arg, [Sm5.BIND id]@body)))::cmds in
			let fun_scope_cmds = inner_trans e2 bind_function_cmds in
			Sm5.POP::Sm5.UNBIND::fun_scope_cmds
		| K.CALLV (id, e) ->(* Here *)
			let e_cmds = inner_trans e cmds in
			let tmp_arg = "#arg"^id in
			let store_arg_cmds = Sm5.STORE::(Sm5.PUSH (Sm5.Id tmp_arg))::(Sm5.BIND tmp_arg)::Sm5.MALLOC::e_cmds in
			(* this part is for recursive call, 
			 *	we insert (Sm5.BIND id) so we need one more (arg, C', E') *)
			let help_bind_cmds = (Sm5.PUSH (Sm5.Id id))::store_arg_cmds in
			let fun_call_cmds = Sm5.CALL::(Sm5.PUSH (Sm5.Id tmp_arg))::Sm5.LOAD::(Sm5.PUSH (Sm5.Id tmp_arg))::(Sm5.PUSH (Sm5.Id id))::help_bind_cmds in
			Sm5.POP::Sm5.UNBIND::fun_call_cmds
		| K.CALLR (id, arg_name) ->
			let help_bind_cmds = (Sm5.PUSH (Sm5.Id id))::cmds in
			Sm5.CALL::(Sm5.PUSH (Sm5.Id arg_name))::Sm5.LOAD::(Sm5.PUSH (Sm5.Id arg_name))::(Sm5.PUSH (Sm5.Id id))::help_bind_cmds
		| K.READ id ->
			Sm5.LOAD::(Sm5.PUSH (Sm5.Id id))::Sm5.STORE::(Sm5.PUSH (Sm5.Id id))::Sm5.GET::cmds
		| K.WRITE e ->
			let e_cmds = inner_trans e cmds in
			let store_tmp_cmds = Sm5.STORE::(Sm5.PUSH (Sm5.Id "#tmp"))::(Sm5.BIND "#tmp")::Sm5.MALLOC::e_cmds in
			let stack_value_twice_cmds = Sm5.LOAD::(Sm5.PUSH (Sm5.Id "#tmp"))::Sm5.LOAD::(Sm5.PUSH (Sm5.Id "#tmp"))::store_tmp_cmds in
			Sm5.POP::Sm5.UNBIND::Sm5.PUT::stack_value_twice_cmds
		| _ -> Sm5.empty_command


let rec trans : K.program -> Sm5.command = 
	fun pgm -> List.rev (inner_trans pgm [])

end
