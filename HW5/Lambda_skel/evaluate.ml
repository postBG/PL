(*
 * SNU 4190.310 Programming Languages (Fall 2014)
 *
 * Lambda Calculus
 *)

module Evaluator =
  struct
	exception Error of string
 	
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

    (* String Set for FV *)
	module StringSet = 
		Set.Make(
			struct 
				let compare = Pervasives.compare 
				type t = string 
			end
		)

	let rec set_of_list : string list -> StringSet.t =
		fun lst ->
			List.fold_left (fun set elem -> StringSet.add elem set) StringSet.empty lst

	let rec find_free_variables : Lambda.lexp -> StringSet.t =
		fun lexp ->
			match lexp with
			| Lambda.Id str -> (StringSet.add str StringSet.empty)
			| Lambda.App (lexp1, lexp2) -> 
				let fv1 = find_free_variables lexp1 in
				let fv2 = find_free_variables lexp2 in
				(StringSet.union fv1 fv2)
			| Lambda.Lam (str, new_lexp) -> 
				let fv = find_free_variables new_lexp in
				let str_set = StringSet.add str (StringSet.empty) in
				(StringSet.diff fv str_set)


	let rec find_substitution : (string * string) list -> string -> string =
		fun sub_list str ->
			snd (List.find (fun oldXnew -> (fst oldXnew) = str) sub_list)

	let count = ref 0
	let incr_count n = count := !count + n
	let decr_count n = count := !count - n

	let rec inner_renaming : Lambda.lexp -> string -> string -> Lambda.lexp =
		fun lexp old_str new_str ->
			match lexp with
			| Lambda.Id str -> 
				if str = old_str then Lambda.Id new_str
				else lexp
			| Lambda.Lam (str, inner_lexp) -> 
				if str = old_str then lexp (* bound to str *)			
				else 
					let renamed_lexp = inner_renaming inner_lexp old_str new_str in
					Lambda.Lam (str, renamed_lexp)
			| Lambda.App (lexp1, lexp2) ->
				let renamed_lexp1 = inner_renaming lexp1 old_str new_str in
				let renamed_lexp2 = inner_renaming lexp2 old_str new_str in
				Lambda.App (renamed_lexp1, renamed_lexp2)

	let rec renaming_bound_variables : Lambda.lexp -> Lambda.lexp =
		fun lexp ->
			match lexp with
			| Lambda.Lam (str, inner_lexp) ->
				let rare_renamed_lexp = renaming_bound_variables inner_lexp in
				let new_str = str^(string_of_int (!count)) in
				incr_count 1;
				let renamed_lexp = inner_renaming rare_renamed_lexp str new_str in
				Lambda.Lam (new_str, renamed_lexp)
			| Lambda.App (lexp1, lexp2) ->
				let renamed_lexp1 = renaming_bound_variables lexp1 in
				let renamed_lexp2 = renaming_bound_variables lexp2 in
				Lambda.App (renamed_lexp1, renamed_lexp2)
			| _ -> lexp


	(* this function implements [N/x] M *)
	let rec substitute : Lambda.lexp -> string -> Lambda.lexp -> Lambda.lexp =
		fun lexp target sub ->
			match lexp with
			| Lambda.Id str -> 
				if str = target then sub
				else lexp
			| Lambda.Lam (str, inner_lexp) ->
				if str = target then lexp
				else
					let renamed_lexp = substitute inner_lexp target sub in
					let fv = find_free_variables sub in
					if StringSet.mem target fv then Lambda.Lam (str, renamed_lexp)
					else raise (Error "renaming free variable")
			| Lambda.App (lexp1, lexp2) ->
				let renamed_lexp1 = substitute lexp1 target sub in
				let renamed_lexp2 = substitute lexp2 target sub in
				Lambda.App (renamed_lexp1, renamed_lexp2)
					

	let rec reduce : Lambda.lexp -> Lambda.lexp = 
		fun exp -> raise (Error "not implemented")

  end
