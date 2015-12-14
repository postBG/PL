(*
 * SNU 4190.310 Programming Languages 2015 Fall
 * Type Checker Skeleton
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open M

type var = string

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
  (* Modify, or add more if needed *)

type typ_scheme =
  | SimpleTyp of typ 
  | GenTyp of (var list * typ)

type typ_env = (M.id * typ_scheme) list

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

(* Definitions related to free type variable *)

let union_ftv ftv_1 ftv_2 = 
  let ftv_1' = List.filter (fun v -> not (List.mem v ftv_2)) ftv_1 in
  ftv_1' @ ftv_2
  
let sub_ftv ftv_1 ftv_2 =
  List.filter (fun v -> not (List.mem v ftv_2)) ftv_1

let rec ftv_of_typ : typ -> var list = function
  | TInt | TBool | TString -> []
  | TPair (t1, t2) -> union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TLoc t -> ftv_of_typ t
  | TFun (t1, t2) ->  union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TVar v -> [v]

let ftv_of_scheme : typ_scheme -> var list = function
  | SimpleTyp t -> ftv_of_typ t
  | GenTyp (alphas, t) -> sub_ftv (ftv_of_typ t) alphas 

let ftv_of_env : typ_env -> var list = fun tyenv ->
  List.fold_left 
    (fun acc_ftv (id, tyscm) -> union_ftv acc_ftv (ftv_of_scheme tyscm))
    [] tyenv 

(* Generalize given type into a type scheme *)
let generalize : typ_env -> typ -> typ_scheme = fun tyenv t ->
  let env_ftv = ftv_of_env tyenv in
  let typ_ftv = ftv_of_typ t in
  let ftv = sub_ftv typ_ftv env_ftv in
  if List.length ftv = 0 then
    SimpleTyp t
  else
    GenTyp(ftv, t)

(* Definitions related to substitution *)

type subst = typ -> typ

let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = 
  fun x t ->
    let rec subs t' = 
      match t' with
      | TVar x' -> if (x = x') then t else t'
      | TPair (t1, t2) -> TPair (subs t1, subs t2)
      | TLoc t'' -> TLoc (subs t'')
      | TFun (t1, t2) -> TFun (subs t1, subs t2)
      | TInt | TBool | TString -> t'
    in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t)) (* substitution composition *)

let subst_scheme : subst -> typ_scheme -> typ_scheme = 
  fun subs tyscm ->
    match tyscm with
    | SimpleTyp t -> SimpleTyp (subs t)
    | GenTyp (alphas, t) ->
      (* S (\all a.t) = \all b.S{a->b}t  (where b is new variable) *)
      let betas = List.map (fun _ -> new_var()) alphas in
      let s' =
        List.fold_left2
          (fun acc_subst alpha beta -> make_subst alpha (TVar beta) @@ acc_subst)
          empty_subst alphas betas
      in
      GenTyp (betas, subs (s' t))

let subst_env : subst -> typ_env -> typ_env = 
  fun subs tyenv ->
    List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv

(*---------------------------------------------------------------------*)
let rec occurs : var -> typ -> bool =
  fun x t ->
    match t with
    | TInt -> false
    | TBool -> false
    | TString -> false
    | TPair (t1, t2) -> (occurs x t1) || (occurs x t2)
    | TLoc t' -> (occurs x t')
    | TFun (t1, t2) -> (occurs x t1) || (occurs x t2)
    | TVar x' -> x = x'

let rec unify : (typ * typ) -> subst =
  fun tXt' ->
    let (t, t') = tXt' in
    match (t, t') with
    | (TInt, TInt) -> empty_subst
    | (TBool, TBool) -> empty_subst
    | (TString, TString) -> empty_subst
    | (TVar x, tau) ->
      if t = t' then empty_subst
      else if (occurs x tau) then raise (M.TypeError "fail: occur in tau")
      else make_subst x tau
    | (tau, TVar x) -> unify(t', t)
    | (TFun (tau1, tau2), TFun (tau1', tau2')) ->
      let s = unify(tau1, tau1') in
      let s' = unify(s tau2, s tau2') in
      (s' @@ s)
    | (TPair (tau1, tau2), TPair (tau1', tau2')) ->
      let s = unify(tau1, tau1') in
      let s' = unify(s tau2, s tau2') in
      (s' @@ s)
    | (TLoc tau1, TLoc tau2) -> unify(tau1, tau2)
    | _ -> raise (M.TypeError "fail: in unify")

let write_var = ref []
let eq_var = ref []

let rec apply_env : typ_env -> M.id -> typ_scheme =
  fun env x ->
    try
      List.assoc x env
    with Not_found -> raise (M.TypeError ("fail: "^x^"is not in env"))

let rec instantiate_alphas : var list -> subst -> subst =
  fun alphas s ->
    match alphas with
    | [] -> s
    | alpha::tail ->
        let beta = (TVar (new_var())) in
        let sub = make_subst alpha beta in
        (instantiate_alphas tail sub) @@ s 

let rec instantiate : typ_scheme -> typ =
  fun typ_sch ->
    match typ_sch with
    | SimpleTyp t -> t
    | GenTyp (alphas, t) -> 
        let s = (instantiate_alphas alphas empty_subst) in
        s t


let rec expansive : M.exp -> bool =
  fun exp ->
    match exp with
    | M.CONST const -> false
    | M.VAR id -> false
    | M.FN (id, exp) -> false 
    | M.APP (e1, e2) -> true
    | M.LET (M.VAL (id, e1), e2) -> 
        (expansive e1) || (expansive e2)
    | M.LET (M.REC (id, x, body), e2) -> 
        let e1 = M.FN (x, body) in 
        (expansive e1) || (expansive e2)
    | M.IF (e1, e2, e3) -> 
        (expansive e1) || (expansive e2) || (expansive e3)
    | M.BOP (bop, e1, e2) -> 
        (expansive e1) || (expansive e2)
    | M.READ -> false
    | M.WRITE exp -> expansive exp
    | M.MALLOC exp -> true       
    | M.ASSIGN (e1, e2) -> (expansive e1) || (expansive e2)
    | M.BANG exp -> expansive exp
    | M.SEQ (e1, e2) -> (expansive e1) || (expansive e2)     
    | M.PAIR (e1, e2) -> (expansive e1) || (expansive e2)
    | M.FST exp -> (expansive exp)         
    | M.SND exp -> (expansive exp)        

let rec m_algorithm : typ_env -> M.exp -> typ -> subst =
  fun env exp tau ->
    match exp with
    | M.CONST (M.N n) -> unify (tau, TInt)
    | M.CONST (M.B b) -> unify (tau, TBool)
    | M.CONST (M.S s) -> unify (tau, TString)
    | M.VAR id -> 
        let typ_sch = apply_env env id in 
        let new_typ = instantiate typ_sch in 
        unify (tau, new_typ)
    | M.FN (id, e) ->
        let alpha1 = TVar (new_var()) in
        let alpha2 = TVar (new_var()) in
        let s = unify (tau, TFun (alpha1, alpha2)) in
        let new_elem = (id, SimpleTyp (s alpha1)) in
        let new_env = new_elem::(subst_env s env) in
        let s' = m_algorithm new_env e (s alpha2) in
        (s' @@ s)
    | M.APP (e1, e2) ->
        let alpha = TVar (new_var()) in
        let s = m_algorithm env e1 (TFun (alpha, tau)) in
        let new_env = subst_env s env in
        let s' = m_algorithm new_env e2 (s alpha) in
        (s' @@ s)
    | M.LET (M.VAL (id, e1), e2) ->
        let alpha = TVar (new_var()) in
        let s = m_algorithm env e1 alpha in
        let gen_typ = generalize (subst_env s env) (s alpha) in
        let new_env = (id, gen_typ)::(subst_env s env) in
        let s' = m_algorithm new_env e2 (s tau) in
        (s' @@ s)
    | M.LET (M.REC (id, x, body), e2) ->
        let e1 = M.FN (x, body) in
        let is_safe = not (expansive e1) in
        let alpha1 = TVar (new_var()) in
        let alpha2 = TVar (new_var()) in

        let new_typ = (TFun (alpha1, alpha2)) in
        let gen_typ1 = generalize env new_typ in
        let new_env1 = (if is_safe then (id, gen_typ1) else (id, SimpleTyp new_typ))::env in 
        let s = m_algorithm new_env1 e1 new_typ in

        let new_env2 = subst_env s env in
        let gen_typ2 = generalize new_env2 (s new_typ) in 
        let new_env3 = (if is_safe then (id, gen_typ2) else (id, SimpleTyp (s new_typ)))::new_env2 in 
        let s' = m_algorithm new_env3 e2 (s tau) in
        (s' @@ s)
    | M.IF (e1, e2, e3) ->
        let s = m_algorithm env e1 TBool in 
        let new_env1 = subst_env s env in 
        let s' = m_algorithm new_env1 e2 (s tau) in
        let new_env2 = subst_env s' new_env1 in 
        let s'' = m_algorithm new_env2 e3 (s' (s tau)) in
        (s'' @@ (s' @@ s))
    | M.READ -> unify (tau, TInt)
    | M.WRITE e ->
        write_var := tau::(!write_var);
        (m_algorithm env e tau)
    | M.MALLOC e ->
        let alpha = TVar (new_var()) in 
        let s = unify (tau, TLoc alpha) in
        let new_env = subst_env s env in 
        let s' = m_algorithm new_env e (s alpha) in
        (s' @@ s)
    | M.ASSIGN (e1, e2) ->
        let s = m_algorithm env e1 (TLoc tau) in 
        let new_env = subst_env s env in
        let s' = m_algorithm new_env e2 (s tau) in
        (s' @@ s)
    | M.BANG e -> m_algorithm env e (TLoc tau)
    | M.SEQ (e1, e2) ->
        let alpha = TVar (new_var()) in
        let s = m_algorithm env e1 alpha in
        let new_env = subst_env s env in 
        let s' = m_algorithm new_env e2 (s tau) in
        (s' @@ s)
    | M.PAIR (e1, e2) ->
        let alpha1 = TVar (new_var()) in
        let alpha2 = TVar (new_var()) in
        let s = unify (tau, TPair (alpha1, alpha2)) in
        let new_env1 = subst_env s env in 
        let s' = m_algorithm new_env1 e1 (s alpha1) in
        let new_env2 = subst_env s' new_env1 in 
        let s'' = m_algorithm new_env2 e2 (s' (s alpha2)) in
        (s'' @@ (s' @@ s))
    | M.FST e ->
        let alpha = TVar (new_var()) in 
        m_algorithm env e (TPair (tau, alpha))
    | M.SND e ->
        let alpha = TVar (new_var()) in 
        m_algorithm env e (TPair (alpha, tau))    
    | M.BOP (bop, e1, e2) ->
        (match bop with
        | M.ADD -> bop_check env e1 e2 tau TInt
        | M.SUB -> bop_check env e1 e2 tau TInt
        | M.AND -> bop_check env e1 e2 tau TBool
        | M.OR -> bop_check env e1 e2 tau TBool
        | M.EQ -> 
            let alpha = TVar (new_var()) in
            eq_var := alpha::(!eq_var);

            let s = unify (tau, TBool) in
            let new_env1 = subst_env s env in 
            let s' = m_algorithm new_env1 e1 (s alpha) in
            let new_env2 = subst_env s' new_env1 in
            let s'' = m_algorithm new_env2 e2 (s' (s alpha)) in
            (s'' @@ (s' @@ s))
        )
and bop_check : typ_env -> M.exp -> M.exp -> typ -> typ -> subst =
  fun env e1 e2 tau primitive ->
    let s = unify (tau, primitive) in
    let new_env1 = subst_env s env in 
    let s' = m_algorithm new_env1 e1 (s primitive) in
    let new_env2 = subst_env s' new_env1 in 
    let s'' = m_algorithm new_env2 e2 (s' (s primitive)) in
    (s'' @@ (s' @@ s)) 

let rec no_error_write_var lst sub =
    match lst with
    | [] -> true
    | hd::tail ->
      (match (sub hd) with
      | TInt -> true
      | TBool -> true
      | TString -> true
      | _ -> false) && (no_error_write_var tail sub)

let rec no_error_eq_var lst sub =
    match lst with
    | [] -> true
    | hd::tail ->
      (match (sub hd) with
      | TInt -> true
      | TBool -> true
      | TString -> true
      | TLoc ty -> true
      | _ -> false) && (no_error_eq_var tail sub)

let rec typ2type : typ -> M.typ =
    fun typ ->
    match typ with
    | TVar id -> raise (M.TypeError "fail by TVar")
    | TInt -> M.TyInt
    | TBool -> M.TyBool
    | TString -> M.TyString
    | TPair(typ1, typ2) -> M.TyPair (typ2type typ1, typ2type typ2)
    | TLoc typ' -> M.TyLoc (typ2type typ')
    | TFun(typ1, typ2) -> raise (M.TypeError "fail by TFun")

(* TODO : Implement this function *)
let check : M.exp -> M.typ =
  fun exp ->
    let alpha = TVar (new_var()) in 
    let s = m_algorithm [] exp alpha in
    if (no_error_eq_var !eq_var s) && (no_error_write_var !write_var s)
    then typ2type (s alpha)
    else raise (M.TypeError "fail with write var or eq var")