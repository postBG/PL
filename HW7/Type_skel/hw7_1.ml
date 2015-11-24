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
	let rec new_id n = (count := !count + n); "alpha"^(string_of_int (!count))

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
			(fun mty -> 
				match mty with
				| Int -> mty
				| Bool -> mty
				| String -> mty
				| Pair (t1, t2) -> 
						Pair (new_id_mtype_sub id sub_type t1, new_id_mtype_sub id sub_type t2)
				| Loc t -> Loc (new_id_mtype_sub id sub_type t)
				| Arrow (t1, t2) -> 
						Arrow (new_id_mtype_sub id sub_type t1, new_id_mtype_sub id sub_type t2)
				| V in_id -> if id = in_id then sub_type else mty
			) 

	let rec s'_s : substitution -> substitution -> substitution =
		fun s' s -> (fun mty -> s' (s mty))

	let rec s_t : substitution -> tyenvironment -> tyenvironment =
		fun s tyenv -> (fun id -> s (tyenv id))

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
				(s'_s s' s)
			| (Pair (tau1, tau2), Pair (tau1', tau2')) ->
				let s = unify(tau1, tau1') in
				let s' = unify(s tau2, s tau2') in
				(s'_s s' s)
			| (Loc tau, Loc tau') -> unify (tau, tau')
			| _ -> raise (TypeError "fail")
			
	let write_var = ref []
	let eq_var = ref [] 

	let rec w_algorithm : (tyenvironment * exp) -> (mtype * substitution) =
		fun tyenvXexp ->
			let (tyenv, exp) = tyenvXexp in
			match exp with
			| CONST(N n) -> (Int, none)
			| CONST(B b) -> (Bool, none)
			| CONST(S s) -> (String, none)
			| VAR x -> (tyenv x, none)
			| FN (x, e) ->
				let alpha = V (new_id 1) in
				let new_env = update_env tyenv x alpha in
				let (tau, s) = w_algorithm (new_env, e) in
				(Arrow(s alpha, tau), s)
			| APP (e1, e2) -> 
				let (tau, s) = w_algorithm(tyenv, e1) in
				let (tau', s') = w_algorithm(s_t s tyenv, e2) in
				let alpha = V (new_id 1) in
				let s'' = unify(Arrow(tau', alpha), s' tau) in
				(s'' alpha, s'_s s'' (s'_s s' s))
			| LET (NREC (x, e1), e2) ->
				let (tau, s) = w_algorithm(tyenv, e1) in
				let raw_new_env = update_env tyenv x tau in
				let new_env = s_t s raw_new_env in
				let (tau', s') = w_algorithm(new_env, e2) in
				(tau', s'_s s' s)
			| LET (REC (x, e1), e2) ->
				let alpha1 = V (new_id 1) in
				let alpha2 = V (new_id 1) in
				let new_env1 = update_env tyenv x (Arrow(alpha1, alpha2)) in
				let (tau, s) = w_algorithm(new_env1, e1) in
				let s' = unify (tau, Arrow(alpha1, alpha2)) in
				let new_tau = s' tau in
				let raw_new_env2 = update_env tyenv x new_tau in
				let new_env2  = s_t (s'_s s' s) raw_new_env2 in 
				let (tau', s'') = w_algorithm(new_env2, e2) in
				(tau', s'_s s'' (s'_s s' s))
			| IF(e1, e2, e3) ->
				let (tau1, s1) = w_algorithm(tyenv, e1) in
				let s2 = unify(Bool, tau1) in
				let s3 = s'_s s2 s1 in
				let new_env1 = s_t s3 tyenv in
				let (tau2, s4) = w_algorithm(new_env1, e2) in
				let s5 = s'_s s4 s3 in
				let new_env2 = s_t s5 new_env1 in
				let (tau3, s6) = w_algorithm(new_env2, e3) in
				let s7 = unify(tau2, tau3) in
				let s8 = s'_s s7 (s'_s s6 s5) in
				(s8 tau3, s8)
			| READ -> (Int, none)
			| WRITE e ->
				let (tau, s) = w_algorithm(tyenv, e) in
				write_var := tau::(!write_var);
				(tau, s)
			| MALLOC e ->
				let (tau, s) = w_algorithm(tyenv, e) in
				(Loc tau, s)
			| ASSIGN (e1, e2) ->
				let (tau, s) = w_algorithm(tyenv, e1) in	
				let new_env = s_t s tyenv in
				let (tau', s') = w_algorithm(new_env, e2) in
				let s'' = unify (s' tau, Loc tau') in
				(tau', s'_s s'' (s'_s s' s))
			| BANG e ->
				let (tau, s) = w_algorithm(tyenv, e) in
				(match tau with
					| Loc t -> (tau, s)
					| _ -> raise (TypeError "fail")
				)
			| SEQ(e1, e2) ->
				let (tau, s) = w_algorithm(tyenv, e1) in
				let (tau', s') = w_algorithm(s_t s tyenv, e2) in
				(tau', s'_s s' s)
			| PAIR(e1, e2) ->
				let (tau, s) = w_algorithm(tyenv, e1) in
				let (tau', s') =w_algorithm(s_t s tyenv, e2) in
				(Pair(s' tau, tau'), s'_s s' s)
			| SEL1 e ->
				let (tau, s) = w_algorithm(tyenv, e) in
				let alpha1 = V (new_id 1) in
				let alpha2 = V (new_id 1) in
				let s' = unify (Pair (alpha1, alpha2), tau) in
				((s'_s s' s) alpha1, s'_s s' s)
			| SEL2 e ->
				let (tau, s) = w_algorithm(tyenv, e) in
				let alpha1 = V (new_id 1) in
				let alpha2 = V (new_id 1) in
				let s' = unify (Pair (alpha1, alpha2), tau) in
				((s'_s s' s) alpha2, s'_s s' s)
			| BOP(bop, e1, e2) ->
				(match bop with
				| ADD -> bop_check tyenv e1 e2 Int
				| SUB -> bop_check tyenv e1 e2 Int
				| AND -> bop_check tyenv e1 e2 Bool
				| OR -> bop_check tyenv e1 e2 Bool
				| EQ -> 
					let (tau, s1) = w_algorithm(tyenv, e1) in
					let (tau', s2) = w_algorithm(s_t s1 tyenv, e2) in
					let s3 = unify(tau, tau') in
					let s4 = s'_s s3 (s'_s s2 s1) in
					eq_var := (s4 tau)::(s4 tau')::(!eq_var);
					(Bool, s4)
				)
	and bop_check : tyenvironment -> exp -> exp -> mtype -> (mtype * substitution) =
		fun tyenv e1 e2 primitive ->
			let (tau, s1) = w_algorithm(tyenv, e1) in
			let s2 = unify (tau, primitive)	in
			let s3 = s'_s s2 s1 in
			let (tau', s4) = w_algorithm(s_t s3 tyenv, e2) in
			let s5 = unify (tau', primitive) in
			let s6 = s'_s s5 (s'_s s4 s3) in
			(primitive, s6)

	let rec no_error_write_var lst sub =
		match lst with
		| [] -> true
		| hd::tail ->
			(match (sub hd) with
			| Int -> true
			| Bool -> true
			| String -> true
			| _ -> false) && (no_error_write_var tail sub)

	let rec no_error_eq_var lst sub =
		match lst with
		| [] -> true
		| hd::tail ->
			(match (sub hd) with
			| Int -> true
			| Bool -> true
			| String -> true
			| Loc ty -> true
			| _ -> false) && (no_error_eq_var tail sub)

	let rec mtype2type : mtype -> types =
		fun mtype ->
		match mtype with
		| V id -> raise (TypeError "fail by V")
		| Int -> TyInt
		| Bool -> TyBool
		| String -> TyString
		| Pair(mty1, mty2) -> TyPair (mtype2type mty1, mtype2type mty2)
		| Loc mty -> TyLoc (mtype2type mty)
		| Arrow(mty1, mty2) -> TyArrow(mtype2type mty1, mtype2type mty2)

	let rec check exp = 
		write_var := [];
		eq_var := [];
		let (tau, sub) = w_algorithm(empty_env, exp) in
		if (no_error_write_var (!write_var) sub) && (no_error_eq_var (!eq_var) sub)
		then mtype2type tau
		else raise (TypeError "fail at bop")
end
