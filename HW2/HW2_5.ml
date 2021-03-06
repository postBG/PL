exception FreeVariable

type exp = X
	| INT of int
	| REAL of float
	| ADD of exp * exp
	| SUB of exp * exp
	| MUL of exp * exp
	| DIV of exp * exp
	| SIGMA of exp * exp * exp
	| INTEGRAL of exp * exp * exp

let rec eval (expr, num) =
	match expr with
		| X -> num
		| INT n -> float_of_int n
		| REAL n -> n
		| ADD (e1, e2) -> eval(e1, num) +. eval(e2, num)
		| SUB (e1, e2) -> eval(e1, num) -. eval(e2, num)
		| MUL (e1, e2) -> eval(e1, num) *. eval(e2, num)
		| DIV (e1, e2) -> eval(e1, num) /. eval(e2, num)
		| SIGMA (e1, e2, e3) -> eval_sigma(int_of_float (eval(e1, num)), int_of_float (eval(e2, num)), e3) 0.0
		| INTEGRAL (e1, e2, e3) -> eval_integral(eval(e1, num), eval(e2, num), e3) 0.0
and eval_sigma (n, e, expr) sum =
	if(n > e) then sum
	else eval_sigma(n+1, e, expr) (sum +. eval(expr, float_of_int n))
and eval_integral (n, e, expr) sum =
	if(n > e) then -1.0 *. (eval_integral(e, n, expr) sum)
	else if(e -. n < 0.1) then sum
	else eval_integral(n +. 0.1, e, expr) (sum +. (0.1 *. eval(expr, n))) 
	

 
let rec galculator: exp -> float =
	fun exp ->
		match exp with
		| X -> raise (FreeVariable)
		| INT num -> float_of_int num
		| REAL num -> num
		| ADD (e1, e2) -> (galculator e1) +. (galculator e2)
		| SUB (e1, e2) -> (galculator e1) -. (galculator e2)
		| MUL (e1, e2) -> (galculator e1) *. (galculator e2)
		| DIV (e1, e2) -> (galculator e1) /. (galculator e2)
		| SIGMA (e1, e2, e3) -> eval_sigma((int_of_float (galculator e1)), (int_of_float (galculator e2)), e3) 0.0
		| INTEGRAL (e1, e2, e3) -> eval_integral(galculator e1, galculator e2, e3) 0.0



