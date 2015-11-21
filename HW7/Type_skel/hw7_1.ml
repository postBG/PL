(*
 * SNU 4190.310 Programming Languages (Fall 2012)
 *
 * Low Fat M: static type checking + interpreter without dynamic type checking
 *)

open M
module M_SimChecker : M_SimTypeChecker = struct
	
	(* mtype = Type *)
	type mtype =
		| Int
		| Bool
		| String
		| Pair of mtype * mtype
		| Loc of mtype
		| Arrow of mtype * mtype
		| V of id (* unknown type variable *)
	and id = string
	
	(* folded function *)
	type tyenvironment = id -> mtype 
	
	(* folded function *)
	(* V -> [Primitive, Pair, Loc, Arrow] *)
	(* concretely, substitution is V id -> mtype *)
	type substitution = mtype -> mtype

	let count = ref 0
	let rec new_id n = (count := !count + n); !count 

	let rec update_env : tyenvironment -> id -> mtype -> tyenvironment =
		fun env id ans_type ->
			(fun x -> if x = id then ans_type else env x)

	let rec empty_env = fun _ -> raise (TypeError "empty env")

	let rec none : mtype -> mtype =
		fun x -> x

	let rec occur : id -> mtype -> bool =
		fun id tau ->
			match tau with
				| Pair (typ1, typ2) -> (occur id typ1) || (occur id typ2)
				| Loc typ -> (occur id typ)
				| Arrow (typ1, typ2) -> (occur id typ1) || (occur id typ2)
				| V id' -> (id = id')
				| _ -> false			

	let rec new_id_mtype_sub : id -> mtype -> substitution =
		fun id sub_type ->
			let new_sub = new_id_mtype_sub id sub_type in
			(fun x -> 
				match x with
				| Int -> x
				| Bool -> x
				| String -> x
				| Pair (t1, t2) -> Pair (new_sub t1, new_sub t2)
				| Loc t -> Loc (new_sub t)
				| Arrow (t1, t2) -> Arrow (new_sub t1, new_sub t2)
				| V in_id -> if id = in_id then sub_type else x
			) 

	let rec relay_sub : substitution -> substitution -> substitution =
		fun s' s -> (fun x -> s' (s x))

	let rec unify : (mtype * mtype) -> substitution =
		fun tXt' ->
			let (t, t') = tXt' in
			match (t, t') with
			| (Int, Int) -> none
			| (Bool, Bool) -> none
			| (String, String) -> none
			| (V id, tau) ->
				if t = t' then none
				else if (occur id tau) then raise (TypeError "fail")
				else new_id_mtype_sub id tau
			| (tau, V id) -> unify(t', t)
			| (Arrow (tau1, tau2), Arrow (tau1', tau2')) ->
				let s = unify(tau1, tau1') in
				let s' = unify(s tau2, s tau2') in
				(relay_sub s' s)
			| (Pair (tau1, tau2), Pair (tau1', tau2')) ->
				let s = unify(tau1, tau1') in
				let s' = unify(s tau2, s tau2') in
				(relay_sub s' s)
			| _ -> raise (TypeError "fail")
				
	let rec m_algorithm : (tyenvironment * exp * mtype) -> substitution =
		fun tyenvXexpXtau ->
			let (tyenv, exp, tau) = tyenvXexpXtau in
			match exp with
			| CONST (N num) -> unify (Int, tau)
			| CONST (B b) -> unify (Bool, tau)
			| CONST (S str) -> unify (String, tau)
			| Var x -> 
				let tau' = tyenv x in
				unify (tau, tau')
			| Fn (x, e) ->


	let rec check exp = raise (TypeError "no checker") (* TODO: implementation *)
end
