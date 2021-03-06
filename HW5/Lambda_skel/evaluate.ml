(*
 * SNU 4190.310 Programming Languages (Fall 2014)
 *
 * Lambda Calculus
 *)

module Evaluator =
  struct
	exception Error of string

	let count = ref 0
	let incr_count n = count := !count + n
	let decr_count n = count := !count - n

	let make_new_name : string -> string =
		fun str ->
			incr_count 1;
			str^(string_of_int (!count))

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
				let new_str = make_new_name str in
				let renamed_lexp = inner_renaming rare_renamed_lexp str new_str in
				Lambda.Lam (new_str, renamed_lexp)
			| Lambda.App (lexp1, lexp2) ->
				let renamed_lexp1 = renaming_bound_variables lexp1 in
				let renamed_lexp2 = renaming_bound_variables lexp2 in
				Lambda.App (renamed_lexp1, renamed_lexp2)
			| _ -> lexp


	(* this function implements [N/x] M *)
	let rec substitute : string -> Lambda.lexp -> Lambda.lexp -> Lambda.lexp =
		fun prev after lexp ->
			match lexp with
			| Lambda.Id str ->
				if str = prev then after
				else lexp
			| Lambda.Lam (str, inner_lexp) ->
				if str = prev 
				then 
					(* raise Error("cannot be happen") *)
					let renamed = renaming_bound_variables lexp in
					substitute prev after renamed
				else
					let inner_substituted = substitute prev after inner_lexp in
					Lambda.Lam (str, inner_substituted)
			| Lambda.App (lexp1, lexp2) ->
				let inner_substituted1 = substitute prev after lexp1 in
				let inner_substituted2 = substitute prev after lexp2 in
				Lambda.App (inner_substituted1, inner_substituted2)

	let rec beta_reduction : Lambda.lexp -> Lambda.lexp =
		fun lexp ->
			match lexp with
			| Lambda.App(Lambda.Lam(x, m), n) -> substitute x n m
			| Lambda.Lam(x, m) ->
				let beta_m = beta_reduction m in
				Lambda.Lam(x, beta_m)
			| Lambda.App(Lambda.App(lexp1, lexp2), lexp3) ->
				let tmp_lexp = Lambda.App(lexp1, lexp2) in
				let reduced_lexp = beta_reduction (tmp_lexp) in
				if reduced_lexp = tmp_lexp 
				then Lambda.App(tmp_lexp, beta_reduction lexp3)
				else Lambda.App(reduced_lexp, lexp3)
			| Lambda.App(lexp1, lexp2) ->
				let beta_lexp1 = beta_reduction lexp1 in
				let beta_lexp2 = beta_reduction lexp2 in
				Lambda.App(beta_lexp1, beta_lexp2)
			| _ -> lexp

	let rec inner_reduce : Lambda.lexp -> Lambda.lexp =
		fun lexp ->
			let reduced_lexp = beta_reduction lexp in
			if lexp = reduced_lexp then lexp
			else 
				try
					inner_reduce reduced_lexp
				with (Error "cannot be happen") ->
					let renamed = renaming_bound_variables reduced_lexp in
					inner_reduce renamed
			

	let rec reduce : Lambda.lexp -> Lambda.lexp = 
		fun exp -> 
			let preprocessed = renaming_bound_variables exp in
			inner_reduce preprocessed 

  end