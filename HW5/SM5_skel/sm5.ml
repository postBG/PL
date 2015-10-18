(*
 * SNU 4190.310 Programming Languages (Fall 2014)
 *
 * SM5
 *)

module type SM5 = 
sig
  type cmd = 
         PUSH of obj | POP | STORE | LOAD | JTR of command * command
       | MALLOC | BOX of int | UNBOX of string | BIND of string | UNBIND
       | GET | PUT | CALL | ADD | SUB | MUL | DIV | EQ | LESS | NOT
   and obj = Val of value | Id of string | Fn of string * command
   and value = Z of int | B of bool | L of loc | Unit | R of record
   and record
   and loc
   and command = cmd list

  exception GC_Failure

  val empty_command : command

  val print : command -> unit
  val run : command -> unit

end

module Sm5 : SM5 =
struct
    type cmd = 
           PUSH of obj | POP | STORE | LOAD | JTR of command * command
         | MALLOC | BOX of int | UNBOX of string | BIND of string | UNBIND
         | GET | PUT | CALL | ADD | SUB | MUL | DIV | EQ | LESS | NOT
     and obj = Val of value | Id of string | Fn of string * command
     and svalue = V of value | P of proc | M of map
     and value = Z of int | B of bool | L of loc | Unit | R of record
     and record = map list
     and loc = int * int
     and map = string * svalue
     and proc = string * command * environment
     and stack = svalue list
     and memory = (loc * value) list
     and environment = map list
     and command = cmd list
     and continuation = (command * environment) list
     
    exception GC_Failure
    exception RunError of stack * memory * environment * command * continuation
    exception Unbound_id of string
    exception Unbound_loc of int * int
    exception End
    
    let empty_command = []

    let (@?) l x = snd (List.find (fun y -> x = fst y) l)
    let fsts l = List.map fst l 
    let rec rangecheck l r1 r2 =
    	match l with
  	  [] -> true
  	| h::tl -> ((r1 @? h) = (r2 @? h)) && (rangecheck tl r1 r2)

    open Format

    let rec print_seq f g l =
      match l with
        [] -> ()
      | [h] -> f h
      | h::t -> f h; g h; print_seq f g t

    let rec printv v =
      match v with
        Z i -> printf "%d" i
      | B b -> if b then printf "true" else printf "false"
      | R [] -> printf "[]"
      | R (h::t) ->
          let pf t = 
  			match t with
  			  (x, V(L(l1, l2))) -> printf "(%s,<%d,%d>)" x l1 l2
              | _ -> raise (Invalid_argument "non Loc in Record")
          in  printf "["; pf h; List.iter (fun f -> printf ", "; pf f) t; 
              printf "]"
      | Unit -> printf "()" 
      | L (b,o) -> printf "<%d,%d>" b o
    let rec printp p = 
      match p with
        Val v -> printv v
      | Id x -> printf "%s" x
      | Fn(x,c) -> printf "@[<1>(%s,@ " x; print c; printf ")@]"
    and printc c = printf "@[";
      (match c with
           PUSH p -> printf "push "; printp p
         | POP -> printf "pop"
         | STORE -> printf "store"
         | LOAD -> printf "load"
         | JTR(c1,c2) -> 
             printf "@[<5>jtr ("; print c1; printf ",@ ";
             print c2; printf ")@]"
         | MALLOC -> printf "malloc"
         | BOX z -> printf "box %d" z
         | UNBOX x -> printf "unbox %s" x
         | BIND x -> printf "bind %s" x
         | UNBIND -> printf "unbind"
         | GET -> printf "get"
         | PUT -> printf "put"
         | CALL -> printf "call"
         | ADD -> printf "add"
         | SUB -> printf "sub"
         | MUL -> printf "mul"
         | DIV -> printf "div"
         | EQ -> printf "eq"
         | LESS -> printf "less"
         | NOT -> printf "not"); printf "@]"
    and print l =
      printf "@[";
      print_seq printc (fun _ -> printf "@ ") l;
      printf "@]";
      print_flush()
      
    let loccount = ref 0
        (* create new loc *)
    let newl () = loccount := !loccount + 1; (!loccount,0)

    (***********************************************************************)
    (***********************************************************************)
    (***********************************************************************)
    
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

    (* mark and sweep using dfs *)
    let max_mem_size = 128
    let allocated_size = ref 0

    (* inc_size and dec_size should be positive *)
    let increase_allocated_size : int -> unit =
      fun inc_size -> allocated_size := !allocated_size + inc_size
    let decrease_allocated_size : int -> unit =
      fun dec_size -> allocated_size := !allocated_size - dec_size

    (* memory = (loc * value) list *)
    let rec find_value_at_loc : memory -> loc -> value =
      fun memory loc -> 
          snd (List.find (fun locXvalue -> (fst locXvalue = loc)) memory)

    (* find all reachable locations using enviroment *)
    (* enviroment : map list 
     * map = string * svalue 
     * svalue = V of value | P of proc | M of map
     * value = Z of int | B of bool | L of loc | Unit | R of record *)
    (* record = map list *)
    let rec find_reachable_locs : memory -> environment -> loc list =
      fun memory env ->
        match env with
        | [] -> []
        | hd::tail ->
            let sval = snd hd in
            (match sval with
            | V (L loc) -> (* this variable is pointer or reference *)
                (loc_find_reachable_locs memory loc)@(find_reachable_locs memory tail)
            | V (R record) -> (* this varible is start of record *)
                (record_find_reachable_locs memory record)@(find_reachable_locs memory tail)
            | P (_, _, proc_env) -> 
                (find_reachable_locs memory proc_env)@(find_reachable_locs memory tail)
            | M map -> 
                (map_find_reachable_locs memory map)@(find_reachable_locs memory tail)
            | _ -> (find_reachable_locs memory tail)
            )
    and loc_find_reachable_locs : memory -> loc -> loc list =
      fun memory loc ->
        try
          let value = find_value_at_loc memory loc in
          match value with
          | L new_loc -> loc::(loc_find_reachable_locs memory new_loc)
          | R record -> loc::(record_find_reachable_locs memory record)
          | _ -> loc::[] (* end of search *)
        with Not_found -> loc::[] (* end of search *)
    and record_find_reachable_locs : memory -> record -> loc list =
      fun memory record -> 
        match record with
        | [] -> []
        | hd::tail -> (* hd = map = string * svalue *)
            let sval = snd hd in
            (match sval with
            | V (L loc) -> loc::(record_find_reachable_locs memory tail)
            | V (R new_record) -> 
                (record_find_reachable_locs memory new_record)@(record_find_reachable_locs memory tail)
            | P (_, _, proc_env) -> 
                (find_reachable_locs memory proc_env)@(record_find_reachable_locs memory tail)    
            | M map -> 
                (map_find_reachable_locs memory map)@(record_find_reachable_locs memory tail)
            | _ -> (record_find_reachable_locs memory tail)
            )
    and map_find_reachable_locs : memory -> map -> loc list =
      fun memory map ->
        let sval = snd map in
        match sval with
        | V (L loc) -> (loc_find_reachable_locs memory loc)
        | V (R record) -> (record_find_reachable_locs memory record)
        | P (_, _, proc_env) -> (find_reachable_locs memory proc_env)
        | M new_map -> (map_find_reachable_locs memory new_map)
        | _ -> []

    let rec find_all_reachable_locs : memory -> environment -> continuation -> loc list =
      fun memory env k ->
        match k with
        | [] -> (find_reachable_locs memory env)
        | hd::tail ->
            let conti_env = snd hd in
            (find_reachable_locs memory conti_env)@(find_all_reachable_locs memory env tail)

    let rec is_mem_reachable : loc list -> (loc * value) -> bool =
      fun all_locs (loc, value) -> List.mem loc all_locs

    let rec find_all_reachable_mem : memory -> loc list -> memory =
      fun memory all_locs ->
        List.find_all (is_mem_reachable all_locs) memory 

    let rec find_reachable_memory : memory -> environment -> continuation -> memory =
      fun memory env k ->
        let rare_all_reachable_locs = find_all_reachable_locs memory env k in
        let all_reachable_locs = remove_duplicates rare_all_reachable_locs in
        let all_reachable_locs_size = List.length all_reachable_locs in
        let all_reachable_mem = find_all_reachable_mem memory all_reachable_locs in
        decrease_allocated_size(!allocated_size - all_reachable_locs_size);
        all_reachable_mem

    let rec is_mem_enough : unit -> bool =
      fun u -> (!allocated_size < max_mem_size)

    let rec allocate_memory(s, m, e, c, k) =
      if is_mem_enough() then
        (increase_allocated_size(1);
        (V(L(newl()))::s, m, e, c, k))
      else(* garbage collection here!! *)
        (let all_reachable_mem = (find_reachable_memory m e k) in
        if is_mem_enough() then
          (allocate_memory (s, all_reachable_mem, e, c, k))
        else
          raise GC_Failure)

    (***********************************************************************)
    (***********************************************************************)
    (***********************************************************************)
    let rec eval (s,m,e,c,k) = 
      eval(
        match (s,m,e,c,k) with
        | (_,_,_,PUSH(Val v)::c,_) -> (V v::s, m, e, c, k)
        | (_,_,_,PUSH(Id x)::c, _) ->
          (try ((e @? x)::s, m, e, c, k) 
          with Not_found -> raise (Unbound_id x))
        | (_,_,_,PUSH(Fn(x,c'))::c,_) -> (P(x,c',e)::s, m, e, c, k)
        | (w::s,_,_,POP::c,k) -> (s, m, e, c, k)
        | (V(L l)::V v::s,_,_,STORE::c,_) -> (s, (l,v)::m, e, c, k)
        | (V(L l)::s,_,_,LOAD::c,_) -> 
          (try (V(m @? l)::s, m, e, c, k)
          with Not_found -> let (l1, l2) = l in raise (Unbound_loc (l1, l2)))
        | (V(B b)::s,_,_,JTR(c1,c2)::c,_) -> (s, m, e, (if b then c1@c else (c2@c)), k)
        | (_,_,_,MALLOC::c,_) -> allocate_memory(s, m, e, c, k)
        | (_,_,_,BOX z::c,_) ->
          let rec box b i s =
            if i = 0 then V (R b)::s
            else 
  				    match s with 
  				    | (M m::s) -> box (m::b) (i-1) s
              | _ -> raise (RunError (s,m,e,c,k))
            in  (box [] z s, m, e, c, k)
        | (V (R b)::s,_,_,UNBOX x::c,_) ->
            (try ((b @? x)::s,m,e,c,k)
            with Not_found -> raise (Unbound_id x))
        | (w::s,_,_,BIND x::c,_) -> (s, m, (x,w)::e, c, k)
        | (_,_,i::e,UNBIND::c,_) -> (M i::s, m, e, c, k)
        | (V(L l)::V v::P(x,c',e')::s,_,_,CALL::c,k) -> 
            (s, (l,v)::m, (x,V(L l))::e', c', (c,e)::k)
        | (_,_,_,[],(c,e')::k) -> (s, m, e', c, k)
        | (_,_,_,GET::c,_) -> (V(Z(read_int()))::s, m, e, c, k) 
        | (V(Z z)::s,_,_,PUT::c,_) -> 
            print_int z; print_newline(); (s, m, e, c, k)
        | (V(Z z2)::V(Z z1)::s,_,_,ADD::c,_) -> (V(Z(z1+z2))::s, m, e, c, k)
        | (V(Z z2)::V(L(l1,z1))::s,_,_,ADD::c,_) -> 
            if z1+z2 >= 0 
            then (V(L(l1,z1+z2))::s, m, e, c, k) 
            else raise (RunError (s,m,e,c,k))
        | (V(L(l2,z2))::V(Z z1)::s,_,_,ADD::c,_) -> 
            if z1+z2 >= 0 
            then (V(L(l2,z1+z2))::s, m, e, c, k)
            else raise (RunError (s,m,e,c,k))
        | (V(Z z2)::V(Z z1)::s,_,_,SUB::c,_) -> (V(Z(z1-z2))::s, m, e, c, k)
        | (V(Z z2)::V(L(l1,z1))::s,_,_,SUB::c,_) -> 
            if z1-z2 >= 0 
            then (V(L(l1,z1-z2))::s, m, e, c, k)
            else raise (RunError (s,m,e,c,k))
        | (V(L(l2,z2))::V(L(l1,z1))::s,_,_,SUB::c,_) -> 
            if l1 = l2 
            then (V(Z(z1-z2))::s, m, e, c, k)
            else raise (RunError (s,m,e,c,k))
        | (V(Z z2)::V(Z z1)::s,_,_,MUL::c,_) -> (V(Z(z1*z2))::s, m, e, c, k)
        | (V(Z z2)::V(Z z1)::s,_,_,DIV::c,_) -> 
            if z2 = 0 
            then raise (RunError (s,m,e,c,k))
            else (V(Z(z1/z2))::s, m, e, c, k) 
        | (V(Z z2)::V(Z z1)::s,_,_,EQ::c,_) -> (V(B(z1=z2))::s, m, e, c, k)
        | (V(B b2)::V(B b1)::s,_,_,EQ::c,_) -> (V(B(b1=b2))::s, m, e, c, k)
        | (V(R r2)::V(R r1)::s,_,_,EQ::c,_) ->
            (V(B(List.sort compare r1 = List.sort compare r2))::s, m, e, c, k)
        | (V Unit::V Unit::s,_,_,EQ::c,_) -> (V(B true)::s, m, e, c, k)
        | (V(L(l2,z2))::V(L(l1,z1))::s,_,_,EQ::c,_) -> (V(B(l1 = l2 && z1 = z2))::s, m, e, c, k)
        | (V _::V _::s,_,_,EQ::c,_) -> (V(B false)::s,m,e,c,k) 
        | (V(Z z2)::V(Z z1)::s,_,_,LESS::c,_) -> (V(B(z1<z2))::s, m, e, c, k)
        | (V(L(z1,z2))::V(L(l1,l2))::s,_,_,LESS::c,_) -> 
            if z1 = l1 
            then (V(B(l2<z2))::s, m, e, c, k)
            else raise (RunError (s,m,e,c,k))
        | (V(B b)::s,_,_,NOT::c,_) -> (V(B(not b))::s, m, e, c, k)
        | (_,_,_,[],[]) -> raise End
        | _ -> raise (RunError (s,m,e,c,k))
      )

    let print_error x = printf "SM5 evaluation error: ";
      (match x with
         Unbound_id x -> printf "unbound id '%s'.@." x
       | Unbound_loc (l1,l2) -> printf "unbound loc (%d,%d).@." l1 l2
       | RunError (_, _, _, _, _) -> printf "stuck configuration.@."
       | x -> raise x);
      print_flush()  

    let run c = 
  	try
  		(ignore (eval ([],[],[],c,[]))) 
      with End -> ()
      | x -> print_error x
end
