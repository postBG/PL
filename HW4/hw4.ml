type treasure = StarBox | NameBox of string

type key = Bar | Node of key * key

type map = End of treasure
		| Branch of map * map
		| Guide of string * map

(* this is my type*)
type term = Variable of string 
			| Term of term * term

type equation = Equ of term * term

exception Error of string
exception IMPOSSIBLE

let rec inner_list_find lst element num =
	match lst with
	| [] -> -1
	| hd::tail ->
		if (fst hd) = element then num
		else inner_list_find tail element (num + 1)

(* list_find finds index of element if element is member of lst
	or else element is not member of lst then it returns -1*)
let rec list_find lst element =
	inner_list_find lst element 0

(* this function make initial equation and substitution *)
let rec initialize : map -> equation list -> (treasure * term) list -> string -> (equation list * term * (treasure * term) list) =
	fun map equations basic_variable default_name ->
		match map with
		| End treasure ->
			let index = list_find basic_variable treasure in
			if index = (-1) then
				(equations, (Variable default_name), (treasure, (Variable default_name))::basic_variable)
			else
				let (trea, treasure_var) = List.nth basic_variable index in
				(equations, treasure_var, basic_variable)
		| Branch (map1, map2) ->
			let (lequations, lvar, lbasic) = initialize map1 equations basic_variable (String.concat "" [default_name; "0"]) in
			let (requations, rvar, rbasic) = initialize map2 lequations lbasic (String.concat "" [default_name; "1"]) in
			let current_term = Variable default_name in
			let new_equation = Equ (lvar, (Term (rvar, current_term))) in
			let new_equations = new_equation::requations in
			(new_equations, current_term, rbasic)
		| Guide (str, map2) ->
			let treasure_form = (NameBox str) in
			let index = list_find basic_variable treasure_form in
			let current_term = Variable default_name in
			if index = (-1) then
				let treasure_var = Variable (String.concat "" [default_name; "0"]) in
				let new_basic = (treasure_form, treasure_var)::basic_variable in
				let (requations, rvar, rbasic) = initialize map2 equations new_basic (String.concat "" [default_name; "1"]) in 
				let new_equation = Equ (current_term, (Term (treasure_var, rvar))) in
				let new_equations = new_equation::requations in
				(new_equations, current_term, rbasic)
			else
				let (trea, treasure_var) = List.nth basic_variable index in
				let (requations, rvar, rbasic) = initialize map2 equations basic_variable (String.concat "" [default_name; "1"]) in
				let new_equation = Equ (current_term, (Term (treasure_var, rvar))) in
				let new_equations = new_equation::requations in
				(new_equations, current_term, rbasic)

(* Substitution Set : (variable * term) list = (term * term) list *)
(* Equation Set : equation list *)

(* temporary substitution: variable -> term = term -> term *)
let rec make_substitution : equation -> (term -> term) =
	fun equation ->
		match equation with
		| Equ (Variable str, term) -> 
			(fun x -> if x = (Variable str) then term else x)
		| _ -> raise (Error("make_substitution: Can't be substitution"))

(* update : (term -> term) -> term -> term 
	1. update of Equation set should be done by left, right each 
	2. update of Substitution set should be done on snd of pair. Because fst of Substitution should be variable 
	3. if term has type Term then update should be done recursively *)
let rec update : (term -> term) -> term -> term =
	fun sub term ->
		match term with
		| Term (term1, term2) -> Term (update sub term1, update sub term2)
		| _ -> sub term

let rec update_equation : (term -> term) -> equation list -> equation list =
	fun sub equations ->
		match equations with
		| [] -> []
		| hd :: tail ->
			(match hd with
			| Equ (term1, term2) ->
				let new_equation = Equ (update sub term1, update sub term2) in
				new_equation::(update_equation sub tail))

let rec update_substitution : (term -> term) -> (term * term) list -> (term * term) list =
	fun sub substitutions ->
		match substitutions with
		| [] -> []
		| hd :: tail ->
			(match hd with
			| (Variable str, term) ->
				let new_substitution = (Variable str, update sub term) in
				new_substitution::(update_substitution sub tail)
			| _ -> raise (Error("Substitution has Error")))

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

let rec find_variables : term -> term list =
	fun term ->
		match term with
		| Term (term1, term2) -> 
			(find_variables term1)@(find_variables term2)
		| Variable str -> [term]

let rec collect_all_variables : equation list -> term list =
	fun equations ->
		match equations with
		| [] -> []
		| hd :: tail ->
			(match hd with
			| Equ (term1, term2) ->
				(find_variables term1)@(find_variables term2)@(collect_all_variables tail))

let rec ready : equation list -> (term * term) list -> (term * term) list =
	fun equations substitutions ->
		match equations with
		| [] -> substitutions
		| hd :: tail ->
			(match hd with
			| Equ (Term (term11, term12), Term (term21, term22)) ->
				if (Term (term11, term12)) = (Term (term21, term22)) then
					(ready tail substitutions)
				else (*decomposition*)
					let new_eq1 = Equ (term11, term21) in
					let new_eq2 = Equ (term12, term22) in
					(ready (new_eq1::new_eq2::tail) substitutions)
			| Equ (Term (term1, term2), Variable str) -> (* exchange *)
				let term = Term (term1, term2) in
				let variable = Variable str in
				let new_eq = Equ (variable, term) in
				(ready (new_eq::tail) substitutions)
			| Equ (Variable str1, Variable str2) ->
				let variable1 = (Variable str1) in
				let variable2 = (Variable str2) in
				if variable1 = variable2 then (ready tail substitutions) (* remove *)
				else (* substitution *)
					let sub = make_substitution hd in
					let new_equations = update_equation sub tail in
					let new_substitutions = (variable1, variable2)::(update_substitution sub substitutions) in
					(ready new_equations new_substitutions)
			| Equ (Variable str, Term (term1, term2)) ->
				let term = Term (term1, term2) in
				let variable = Variable str in
				if List.mem variable (find_variables term) then raise IMPOSSIBLE
				else 
					let sub = make_substitution hd in
					let new_equations = update_equation sub tail in
					let new_substitutions = (variable, term)::(update_substitution sub substitutions) in
					(ready new_equations new_substitutions))


let rec getReady : map -> key list =
	fun map ->
		[]