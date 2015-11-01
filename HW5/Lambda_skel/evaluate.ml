(*
 * SNU 4190.310 Programming Languages (Fall 2014)
 *
 * Lambda Calculus
 *)

module Evaluator =
  struct
	exception Error of string

	type texp = Id of string
	| Lam of string * texp
	| App of texp * texp
	| CId of string

	let rec ttol : texp -> Lambda.lexp =
		fun texp ->
			match texp with
			| Id str -> Lambda.Id str
			| Lam (str, inner_texp) -> Lambda.Lam (str, ttol inner_texp)
			| App (texp1, texp2) -> Lambda.App (ttol texp1, ttol texp2)
			| CId str -> Lambda.Id str

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

	let rec base_ltot : Lambda.lexp -> texp =
		fun lexp ->
			match lexp with
			| Lambda.Id str -> Id str
			| Lambda.Lam (str, inner_lexp) -> Lam (str, base_ltot inner_lexp)
			| Lambda.App (lexp1, lexp2) ->
				App(base_ltot lexp1, base_ltot lexp2)

	let rec ltot : Lambda.lexp -> (Lambda.lexp -> texp) -> texp =
		fun lexp sub ->
			match lexp with
			| Lambda.Id str -> sub lexp
			| Lambda.Lam (str, inner_lexp) ->
				let sub_fun = (fun x -> if x = Lambda.Id str then CId str else sub x) in
				let inner_substituted = ltot inner_lexp sub_fun in
				Lam(str, inner_substituted)
			| Lambda.App (lexp1, lexp2) ->
				let inner_substituted1 = ltot lexp1 sub in
				let inner_substituted2 = ltot lexp2 sub in
				App(inner_substituted1, inner_substituted2)

	(* this function implements [N/x] M *)
	let rec substitute : texp -> (texp -> texp) -> texp =
		fun texp sub ->
			match texp with 
			| Lam (str, inner_texp) ->
				let inner_sub = (fun y -> if y = (CId str) then y else sub y) in
				let inner_substituted = substitute inner_texp inner_sub in
				Lam (str, inner_substituted)
			| App (texp1, texp2) ->
				let inner_substituted1 = substitute texp1 sub in
				let inner_substituted2 = substitute texp2 sub in
				App (inner_substituted1, inner_substituted2)
			| _ -> sub texp

	let rec beta_reduction : texp -> texp =
		fun texp ->
			match texp with
			| App(Lam(x, m), n) -> 
				let sub = (fun y -> if y = (CId x) then n else y) in
				substitute m sub
			| Lam(x, m) ->
				let beta_m = beta_reduction m in
				Lam(x, beta_m)
			| App(App(texp1, texp2), texp3) ->
				let tmp_texp = App(texp1, texp2) in
				let reduced_texp = beta_reduction (tmp_texp) in
				if reduced_texp = tmp_texp 
				then App(reduced_texp, beta_reduction texp3) 
				else App(reduced_texp, texp3)
			| App(texp1, texp2) ->
				(*let beta_texp1 = beta_reduction texp1 in*)
				let beta_texp2 = beta_reduction texp2 in
				App(texp1, beta_texp2)
			| _ -> texp

	let rec inner_reduce : texp -> texp =
		fun texp ->
			let reduced_texp = beta_reduction texp in
			if texp = reduced_texp then texp
			else inner_reduce reduced_texp 
			

	let rec reduce : Lambda.lexp -> Lambda.lexp = 
		fun exp -> 
			let preprocessed_lexp = renaming_bound_variables exp in
			let preprocessed_texp = ltot preprocessed_lexp base_ltot in
			(ttol (inner_reduce preprocessed_texp))

  end
