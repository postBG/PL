(*
 * SNU 4190.310 Programming Languages 
 * Homework "Rozetta" Skeleton
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

exception Error of string

  let dummy_arg = (Sonata.Val (Sonata.Z 0))

  let rec trans_value : Sm5.value -> Sonata.value =
    fun sm5_value ->
      match sm5_value with
      | Sm5.Z n -> Sonata.Z n
      | Sm5.B b -> Sonata.B b
      | Sm5.Unit -> Sonata.Unit
      | Sm5.L _ -> raise (Sonata.Error "Invalid input program : pushing location")
      | Sm5.R _ -> raise (Sonata.Error "Invalid input program : pushing record")
      
  let prev = "#prev" 
  let tmp_store_prev_fun = "#tempbox"
  let store_prev_fun = "#box"

  (* when mode 1 -> need not return, mode 2 -> return *)
  (* key invariant: #prev -> loc (-1, -1) -> (#prev_arg, removed C, E) *)
  let rec trans' : Sm5.command -> int -> Sonata.command =
    fun sm5_cmds mode ->
      match sm5_cmds with
      | (Sm5.PUSH obj)::tail -> 
          (Sonata.PUSH (trans_obj obj))::(trans' tail mode)
      | (Sm5.POP)::tail -> (Sonata.POP)::(trans' tail mode)
      | (Sm5.STORE)::tail -> (Sonata.STORE)::(trans' tail mode)
      | (Sm5.LOAD)::tail -> (Sonata.LOAD)::(trans' tail mode)
      | (Sm5.JTR (cmd1, cmd2))::tail ->
          let sonata_cmd1 = trans' cmd1 2 in
          let sonata_cmd2 = trans' cmd2 2 in
          (Sonata.JTR (sonata_cmd1, sonata_cmd2))::(trans' tail mode)
      | (Sm5.MALLOC)::tail -> (Sonata.MALLOC)::(trans' tail mode)
      | (Sm5.BOX z)::tail -> (Sonata.BOX z)::(trans' tail mode)
      | (Sm5.UNBOX x)::tail -> (Sonata.UNBOX x)::(trans' tail mode)
      | (Sm5.BIND x)::tail -> (Sonata.BIND x)::(trans' tail mode)
      | (Sm5.UNBIND)::tail -> (Sonata.UNBIND)::(trans' tail mode)
      | (Sm5.GET)::tail -> (Sonata.GET)::(trans' tail mode)
      | (Sm5.PUT)::tail -> (Sonata.PUT)::(trans' tail mode)
      | (Sm5.ADD)::tail -> (Sonata.ADD)::(trans' tail mode)
      | (Sm5.SUB)::tail -> (Sonata.SUB)::(trans' tail mode)
      | (Sm5.MUL)::tail -> (Sonata.MUL)::(trans' tail mode)
      | (Sm5.DIV)::tail -> (Sonata.DIV)::(trans' tail mode)
      | (Sm5.EQ)::tail -> (Sonata.EQ)::(trans' tail mode)
      | (Sm5.LESS)::tail -> (Sonata.LESS)::(trans' tail mode)
      | (Sm5.NOT)::tail -> (Sonata.NOT)::(trans' tail mode)
      | (Sm5.CALL)::tail -> 
          let set_up_rec_cmds = set_up_recursive tail in
          set_up_rec_cmds@[(Sonata.CALL)]
      | [] -> 
          if (mode = 1) then
            (Sonata.PUSH (Sonata.Id store_prev_fun))::(Sonata.LOAD)::(* [("prev", prev_loc)]::S *)
              (Sonata.UNBOX prev)::(* prev_loc::S *)
                (Sonata.LOAD)::
                  (Sonata.PUSH dummy_arg)::Sonata.MALLOC::
                    (Sonata.CALL)::[]
          else []
  and trans_obj : Sm5.obj -> Sonata.obj =
    fun sm5_obj ->
      match sm5_obj with
      | Sm5.Val v -> Sonata.Val (trans_value v)
      | Sm5.Id str -> Sonata.Id str
      | Sm5.Fn (str, cmds) -> Sonata.Fn (str, (trans' cmds 1))
  and set_up_recursive : Sm5.command -> Sonata.command = (* exchange box pointer *)  
    fun sm5_cmds -> 
      let store_prev_condition_cmds = store_prev_condition sm5_cmds in
      let store_prev_condition_func = Sonata.Fn("#prev_arg", store_prev_condition_cmds) in

      (Sonata.PUSH (Sonata.Id store_prev_fun))::(Sonata.LOAD)::(*["prev", prev_loc]::S*) 
        (Sonata.MALLOC)::(Sonata.BIND tmp_store_prev_fun)::
          (Sonata.PUSH (Sonata.Id tmp_store_prev_fun))::(Sonata.STORE)::(*"tmp" => tmp_loc => ["prev", prev_loc]::M *)
            (Sonata.PUSH store_prev_condition_func)::
            (Sonata.MALLOC)::(Sonata.BIND prev)::(Sonata.PUSH (Sonata.Id prev))::(Sonata.STORE)::(*prev_loc => <x, C, E>*)
              (Sonata.UNBIND)::(Sonata.BOX 1)::(* [("prev", prev_loc)]::S *)
              (Sonata.PUSH (Sonata.Id store_prev_fun))::(Sonata.STORE)::[](* "store_prev_fun" => store_loc => [("prev", prev_loc)] *)
  and store_prev_condition : Sm5.command -> Sonata.command =
    fun sm5_cmds ->
      let stored_cmds = (trans' sm5_cmds 1) in 
      (Sonata.PUSH (Sonata.Id tmp_store_prev_fun))::(Sonata.LOAD)::
        (Sonata.PUSH (Sonata.Id store_prev_fun))::(Sonata.STORE)::(* recover box first *)
          (Sonata.UNBIND)::(Sonata.POP)::
            stored_cmds
  
      
  (* set #box for key invariant. #box is always in env 
    #box has [("#prev", caller)]*)
  (* where caller = (x, C, E) *)
    let rec trans : Sm5.command -> Sonata.command = 
      fun command -> 
        let end_fun = (Sonata.Fn ("#prev_arg", [])) in
        (*let special_loc = alloc_special_loc() in*)
        (Sonata.PUSH end_fun)::(Sonata.MALLOC)::(Sonata.BIND prev)::(Sonata.PUSH (Sonata.Id prev))::(* dirty env *)
          (Sonata.STORE)::(* prev_loc => <x, C, E> *)
            (Sonata.UNBIND)::(* remain env intact .... ("prev", prev_loc)::S *)
              (Sonata.BOX 1)::(* [("prev", prev_loc)]::S *)
              (Sonata.MALLOC)::(Sonata.BIND store_prev_fun)::(*"store_prev_fun" => store_loc*)
                (Sonata.PUSH (Sonata.Id store_prev_fun))::(Sonata.STORE)::(* "store_prev_fun" => store_loc => [("prev", prev_loc)] *)
                (trans' command 1)
