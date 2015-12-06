(*
 * SNU 4190.310 Programming Languages (Fall 2012)
 *
 * Let-polymorphism with M algorithm
 *)
open M

module M_PolyChecker : M_PolyChecker = struct
	
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

	type mtype_scheme =
		| Simple of mtype
		| ForAll of ((id list) * mtype)

	(* folded function *)
	type tyenvironment = id -> mtype_scheme 
	
	(* folded function *)
	(* V -> [Primitive, Pair, Loc, Arrow] *)
	(* concretely, substitution is V id -> mtype *)
	type substitution = mtype -> mtype

	let count = ref 0
	let rec new_id n = (count := !count + n); "alpha"^(string_of_int (!count))

	let rec update_env : tyenvironment -> id -> mtype_scheme -> tyenvironment =
		fun env id ans_type_scheme ->
			(fun x -> if x = id then ans_type_scheme else env x)

	let rec empty_env = fun _ -> raise (TypeError "empty env")

	let rec not_exist_in_env : tyenvironment -> id -> bool =
		fun tyenv id ->
			try 
				let _ = tyenv id in
				false
			with TypeError _ -> true

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
	
	(* remove duplicate elements in list *)
  let remove_elt e l =
    let rec go l acc = match l with
      | [] -> List.rev acc
      | x::xs when e = x -> go xs acc
      | x::xs -> go xs (x::acc)
    in go l []

  let remove_duplicates l =
    let rec go l acc = match l with
      | [] -> List.rev acc
      | x :: xs -> go (remove_elt x xs) (x::acc)
    in go l []

	(* Id Set for FV *)
	module IdSet = 
		Set.Make(
			struct 
				let compare = Pervasives.compare 
				type t = id 
			end
		)

	let print_set s = IdSet.iter print_endline s

	let rec list2set : id list -> IdSet.t =
		fun lst ->
			List.fold_left (fun set elem -> IdSet.add elem set) IdSet.empty lst

	let rec collect_ftv_in_simple : mtype -> IdSet.t =
		fun tau ->
			match tau with
			| Int -> (IdSet.empty)
			| Bool -> (IdSet.empty)
			| String -> (IdSet.empty)
			| Pair (t1, t2) -> 
					let fv1 = (collect_ftv_in_simple t1) in
					let fv2 = (collect_ftv_in_simple t2) in
					(IdSet.union fv1 fv2)
			| Loc t -> (collect_ftv_in_simple t)
			| Arrow (t1, t2) -> 
					let fv1 = (collect_ftv_in_simple t1) in
					let fv2 = (collect_ftv_in_simple t2) in
					(IdSet.union fv1 fv2)
			| V id -> (IdSet.add id IdSet.empty) 

	let rec collect_ftv_of_scheme : mtype_scheme -> id list =
		fun omega ->
			match omega with
			| Simple tau -> IdSet.elements (collect_ftv_in_simple tau)
			| ForAll (id_lst, tau) -> 
					let ftv_tau = collect_ftv_in_simple tau in
					let alphas = list2set id_lst in
					IdSet.elements (IdSet.diff ftv_tau alphas)

	let rec remove_ftv_env : tyenvironment -> id list -> id list =
		fun tyenv ftv_omega ->
			List.filter (fun x -> (not_exist_in_env tyenv x)) ftv_omega

	let make_gen : tyenvironment -> mtype_scheme -> mtype_scheme =
		fun tyenv omega ->
			let ftv_omega = collect_ftv_of_scheme omega in
			let gen_alphas = remove_ftv_env tyenv ftv_omega in
			match omega with
			| Simple tau -> ForAll (gen_alphas, tau)
			| ForAll (alphas, tau) -> ForAll (gen_alphas, tau)

	


  let check exp = raise (TypeError "no checker") (* TODO: implementation *)
end
