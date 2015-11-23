(*
 * SNU 4190.310 Programming Languages 
 * Homework "Rozetta" Skeleton
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

let nil = (Sonata.Val (Sonata.Unit))
let dummy_arg = (Sonata.Val (Sonata.Z 0))
let prev = "#prev"
let link = "#link"
let call_stack_head = "#function_list"
let prev_arg = "#prev_arg"

let trans_v : Sm5.value -> Sonata.value = function
  | Sm5.Z z  -> Sonata.Z z
  | Sm5.B b  -> Sonata.B b
  | Sm5.L _ -> raise (Sonata.Error "Invalid input program : pushing location")
  | Sm5.Unit -> Sonata.Unit
  | Sm5.R _ -> raise (Sonata.Error "Invalid input program : pushing record")

let call_stack_pop =
  [
    Sonata.PUSH (Sonata.Id call_stack_head);
    Sonata.LOAD;
    Sonata.UNBOX prev;
    Sonata.LOAD; (* <x, C, E>::S *)

    Sonata.PUSH (Sonata.Id call_stack_head);
    Sonata.LOAD;
    Sonata.UNBOX link;
    Sonata.LOAD; (* [list next node]::<x, C, E>::S *)

    Sonata.PUSH (Sonata.Id call_stack_head);
    Sonata.STORE; (* new list head // <x, C, E>::S *)
  ]

(* TODO : complete this function *)
let rec trans_obj : Sm5.obj -> Sonata.obj = function
  | Sm5.Val v -> Sonata.Val (trans_v v)
  | Sm5.Id id -> Sonata.Id id
  | Sm5.Fn (arg, command) -> 
      let body = trans' command in
      let cps = (* start continuation *)
        [
          Sonata.PUSH dummy_arg;
          Sonata.MALLOC;
          Sonata.CALL;
        ] in
      Sonata.Fn (arg, body@call_stack_pop@cps)

(* TODO : complete this function *)
and trans' : Sm5.command -> Sonata.command = function
  | Sm5.PUSH obj :: cmds -> Sonata.PUSH (trans_obj obj) :: (trans' cmds)
  | Sm5.POP :: cmds -> Sonata.POP :: (trans' cmds)
  | Sm5.STORE :: cmds -> Sonata.STORE :: (trans' cmds)
  | Sm5.LOAD :: cmds -> Sonata.LOAD :: (trans' cmds)
  | Sm5.JTR (c1, c2) :: cmds ->  Sonata.JTR (trans' (c1 @ cmds), trans' (c2 @ cmds)) :: []
  | Sm5.MALLOC :: cmds -> Sonata.MALLOC :: (trans' cmds)
  | Sm5.BOX z :: cmds -> Sonata.BOX z :: (trans' cmds)
  | Sm5.UNBOX id :: cmds -> Sonata.UNBOX id :: (trans' cmds)
  | Sm5.BIND id :: cmds -> Sonata.BIND id :: (trans' cmds)
  | Sm5.UNBIND :: cmds -> Sonata.UNBIND :: (trans' cmds)
  | Sm5.GET ::cmds -> Sonata.GET :: (trans' cmds)
  | Sm5.PUT ::cmds -> Sonata.PUT :: (trans' cmds)
  | Sm5.CALL :: cmds -> 
      let continuation = trans_obj (Sm5.Fn (prev_arg, cmds)) in
      [
        (* store continuation *)
        Sonata.PUSH continuation; 
        Sonata.MALLOC;
        Sonata.BIND prev; (* dirty env *)
        Sonata.PUSH (Sonata.Id prev);
        Sonata.STORE; (*prev -> prev_loc -> continuation *)
        Sonata.UNBIND; (* intact env, (prev, prev_loc)::S *)
  
        Sonata.PUSH (Sonata.Id call_stack_head);
        Sonata.LOAD; (* [prev node]::(prev, prev_loc)::S *)
        Sonata.MALLOC;
        Sonata.BIND link; (* dirty env *)
        Sonata.PUSH (Sonata.Id link);
        Sonata.STORE; (* link -> link_loc -> [prev node] *)
        Sonata.UNBIND; (* (link, link_loc)::(prev, prev_loc)::S *)

        Sonata.BOX 2; (* [(link, link_loc);(prev, prev_loc)]::S *)
        Sonata.PUSH (Sonata.Id call_stack_head);
        Sonata.STORE; (* call_stack_head -> call_stack_loc -> [new node] *)

        (* call *)
        Sonata.CALL;
      ] 
  | Sm5.ADD :: cmds -> Sonata.ADD :: (trans' cmds)
  | Sm5.SUB :: cmds -> Sonata.SUB :: (trans' cmds)
  | Sm5.MUL :: cmds -> Sonata.MUL :: (trans' cmds)
  | Sm5.DIV :: cmds -> Sonata.DIV :: (trans' cmds)
  | Sm5.EQ :: cmds -> Sonata.EQ :: (trans' cmds)
  | Sm5.LESS :: cmds -> Sonata.LESS :: (trans' cmds)
  | Sm5.NOT :: cmds -> Sonata.NOT :: (trans' cmds)
  | [] -> []

(* key invariant: always env have link_head
   and don't change link_head's loc *)
let trans : Sm5.command -> Sonata.command = 
  fun command ->
    let last_continuation = (Sonata.Fn (prev_arg, [])) in
    [
      Sonata.PUSH last_continuation;
      Sonata.MALLOC;
      Sonata.BIND prev;(* dirty env *)
      Sonata.PUSH (Sonata.Id prev);
      Sonata.STORE; (* prev -> prev_loc -> <x, C, E> *)
      Sonata.UNBIND; (* intact env, (prev, prev_loc)::S *)

      Sonata.MALLOC;
      Sonata.BIND link; (* dirty env *)
      Sonata.PUSH nil;
      Sonata.PUSH (Sonata.Id link); (* link -> link_loc -> nil *)
      Sonata.STORE;
      Sonata.UNBIND; (* intact env, (link, link_loc)::(prev, prev_loc)::S *)

      Sonata.BOX 2; (* [(link, link_loc)::(prev, prev_loc)]::S *)
      Sonata.MALLOC;
      Sonata.BIND call_stack_head;
      Sonata.PUSH (Sonata.Id call_stack_head);
      Sonata.STORE;(*func_list -> func_list_loc -> [(link, link_loc)::(prev, prev_loc)]*)
    ]@(trans' command)
