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

	let rec reduce : Lambda.lexp -> Lambda.lexp = 
		fun exp -> raise (Error "not implemented")

  end
