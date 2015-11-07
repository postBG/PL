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
	and id = int
	
	(* folded function *)
	type tyenvironment = id -> mtype 
	
	(* folded function *)
	(* V -> [Primitive, Pair, Loc, Arrow] *)
	(* concretely, substitution is V id -> mtype *)
	type substitution = mtype -> mtype

	let count = ref 0
	let rec new_id n = (count := !count + n); !count 

	let rec update_env : tyenvironment -> mtype -> mtype -> tyenvironment =
		fun env solved_var ans_type ->
			match solved_var with
			| V id -> (* x : id *)
					(fun x -> if x = id then ans_type else env x)
			| _ -> raise (TypeError "wrong input")

	let rec base_substitution : mtype -> mtype =
		fun x -> x

	let rec occur : id -> mtype -> bool =
		fun id tau ->
			match tau with
				| Pair (typ1, typ2) -> (occur id typ1) || (occur id typ2)
				| Loc typ -> (occur id typ)
				| Arrow (typ1, typ2) -> (occur id typ1) || (occur id typ2)
				| V id' -> (id = id')
				| _ -> false			

	let rec alpha_substitution : id -> mtype -> substitution =
		fun id sub_type ->
			let alpha_sub = alpha_substitution id sub_type in
			(fun x -> 
				match x with
				| Int -> x
				| Bool -> x
				| String -> x
				| Pair (t1, t2) -> Pair (alpha_sub t1, alpha_sub t2)
				| Loc t -> Loc (alpha_sub t)
				| Arrow (t1, t2) -> Arrow (alpha_sub t1, alpha_sub t2)
				| V in_id -> if id = in_id then sub_type else x
			) 

	let rec relay_sub : substitution -> substitution -> substitution =
		fun s' s -> (fun x -> s' (s x))

	let rec unify : mtype * mtype -> substitution =
		fun tXt' ->
			let (t, t') = tXt' in
			match (t, t') with
			| (Int, Int) -> base_substitution
			| (Bool, Bool) -> base_substitution
			| (String, String) -> base_substitution
			| (V id, tau) -> 
					if (occur id tau) then raise (TypeError "fail")
					else alpha_substitution id tau
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
				

	let rec check exp = raise (TypeError "no checker") (* TODO: implementation *)
end
