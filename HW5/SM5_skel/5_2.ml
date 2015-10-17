(*[Header]*)
open Sm5.Sm5

(* concat command n times *)
let append (n: int) (f: int -> command) (cmd: command) : command = 
    let rec iter i =
        if i = n then []
        else (f i) @ iter (i + 1) in
    cmd @ (iter 0)

(*[Test]*)
(* 1. Simple malloc & use test *)
let cmds1 =
    let cmds =
    append 128 (fun i -> 
        let v = Printf.sprintf "x%d" i in [
            MALLOC;
            BIND v;
            PUSH (Val (Z 1));
            PUSH (Id v);
            STORE;
            ])
    []
    in

    let cmds =
    append 128 
      (fun i -> 
        let v = Printf.sprintf "x%d" i in [
            PUSH (Id v);
            LOAD;
            ADD;
            ]
      ) (cmds @ [PUSH (Val (Z 0))])
    in

    let cmds = cmds @ [PUT] in

    cmds

let _ = run cmds1

(*[Value]
"128"*)

(*[Test]*)
(* 2. Trigger GC Failure (No garbage memory to collect) *)
let cmds2 =
    let cmds = append 129 (fun i -> 
        let v = Printf.sprintf "x%d" i in [
                MALLOC; 
                BIND v; 
                PUSH (Val (Z i));
                PUSH (Id v);
                STORE;
            ])
        [] in

    (* Access all the allocated memory locations, ensuring they must not have been collected *)
    let cmds = append 128 (fun i -> 
        let v = Printf.sprintf "x%d" i in [
            PUSH (Id v);
            LOAD;
            POP;
         ]) cmds in

    cmds

let _ = run cmds2 

(*[Exception]
GC_Failure*)

(*[Test]*)
(* 3. Trigger GC, with one garbage memory to collect *)
let cmds3 = 
    (* To be collected *)
    let cmds = [
        PUSH (Val (Z 1));
        MALLOC;
        STORE;
    ] in

    let cmds = append 127 (fun i -> 
        let v = Printf.sprintf "x%d" i in [
            MALLOC; 
            BIND v; 
            PUSH (Val (Z 1));
            PUSH (Id v);
            STORE;
        ]) cmds in

    (* Trigger GC *)
    let cmds = cmds @ [
        MALLOC;
        BIND "x_new";
        PUSH (Val (Z 10));
        PUSH (Id "x_new");
        STORE;

        PUSH (Id "x_new");
        LOAD;
    ] in

    (* Check if allocated memory location's values are not affected by GC() *)
    let cmds = append 127 (fun i -> 
        let v = Printf.sprintf "x%d" i in [
            PUSH (Id v);
            LOAD;
            ADD;
         ]) cmds in 

    let cmds = cmds @ [PUT] in

    cmds

let _ = run cmds3

(*[Value]
"137"*)

(*[Test]*)
(* 4. Gc must be able to track the list structure, and decide that there's no garbage to collect *) 
let cmds4 = 
    let cmds = [
        MALLOC; 
        BIND "start";
        PUSH (Id "start");
        BIND "cur"; 
    ] in

    let cmds = append 127 (fun _ -> 
        [
            MALLOC;
            PUSH (Id "cur");
            STORE;

            PUSH (Id "cur");
            LOAD;

            UNBIND;
            POP;

            BIND "cur";
        ]) cmds in

    (* Trigger GC *)
    let cmds = cmds @ [
		MALLOC;
     ] in

    (* Access all the allocated memory locations, ensuring they must not have been collected *)
    let cmds = append 127 (fun _ ->
        [LOAD;]
        ) cmds @ [PUSH (Val (Z 1)); PUSH (Id "start");] in
    
    cmds @ [STORE]

let _ = run cmds4

(*[Exception]
GC_Failure*)

(*[Test]*)
(* 5. Alternatedly *)
let cmds5 =
    (* Trigger GC *)
    let cmds =
    append 128 (fun i -> 
        let v = Printf.sprintf "x%d" i in [
            (* To be collected *)
            PUSH (Val (Z 1));
            MALLOC;
            STORE;
            
            (* Not to be collected *)
            MALLOC;
            BIND v;
            PUSH (Val (Z 1));
            PUSH (Id v);
            STORE
            ])
    [] in

    (* Check if allocated memory location's values are not affected by GC() *)
    let cmds =
    append 128 
      (fun i -> 
        let v = Printf.sprintf "x%d" i in [
            PUSH (Id v);
            LOAD;
            ADD;
            ]
      ) (cmds @ [PUSH (Val (Z 0))])
    in

    let cmds = cmds @ [PUT] in

    cmds

let _ = run cmds5

(*[Value]
"128"*)

(*[Test]*)
(* 6. Should not collect location inside BOX *)
let cmds6 =

    let cmds = append 126 (fun i -> 
        let v = Printf.sprintf "x%d" i in [
                MALLOC; 
                BIND v; 
                PUSH (Val (Z i));
                PUSH (Id v);
                STORE;
            ])
    [] in

    let cmds = cmds @ [
            MALLOC;
            BIND "loc";
            
            PUSH (Val (Z 1));
            PUSH (Id "loc");
            STORE;

            UNBIND;
        ]
    in

    let cmds = cmds @ [
        BOX 1;

        MALLOC;
        BIND "rec";

        PUSH (Id "rec"); 
        STORE; 

        (* Trigger GC *)
        PUSH (Val (Z 1));
        MALLOC;
        STORE;
    ] in

    (* Access all the allocated memory locations, ensuring they must not have been collected *)
    let cmds = append 126 (fun i -> 
        let v = Printf.sprintf "x%d" i in [
            PUSH (Id v);
            LOAD;
            POP;
         ]) cmds @ [PUSH (Id "rec"); LOAD; UNBOX "loc"; LOAD] in

    cmds

let _ = run cmds6

(*[Exception]
GC_Failure

[Test]*)
let cmds7 = 
    let cmds = [
        PUSH (Fn ("x", [
            (* Trigger GC *)
            PUSH (Val (Z 1));
            MALLOC;
            STORE;

            (* Access argument location, ensuring it must not have been collected *)
            PUSH (Id "x");
            LOAD;
            POP;
        ]));

        BIND "f";
    ] in

    let cmds = append 127 (fun i -> 
        let v = Printf.sprintf "x%d" i in [
            MALLOC;
            BIND v;
            PUSH (Val (Z i));
            PUSH (Id v);
            STORE
        ]) cmds in

    let cmds = cmds @ [
        PUSH (Id "f");
        PUSH (Val (Z 1));
        MALLOC;
        CALL;

    ] in

    (* Access all the allocated memory locations, ensuring they must not have been collected *)
    let cmds = append 127 (fun i -> 
        let v = Printf.sprintf "x%d" i in [
            PUSH (Id v);
            LOAD;
            POP;
         ]) cmds in
    
    cmds

let _ = run cmds7

(*[Exception]
GC_Failure

[Test]*)
let cmds8 = 

    let cmds = [
        PUSH (Fn ("x", [
            (* Trigger GC *)
            (* At the same time, to be collected in the second call *)
            PUSH (Val (Z 1));
            MALLOC;
            STORE;

            (* Access argument location, ensuring it must not have been collected *)
            PUSH (Id "x");
            LOAD;
            POP;
        ]));

        BIND "f";
    ] in

    let cmds = append 126 (fun i -> 
        let v = Printf.sprintf "x%d" i in [
            MALLOC; 
            BIND v; 
            PUSH (Val (Z 2));
            PUSH (Id v);
            STORE;
        ]) cmds in

    (* First Call *)
    let cmds = cmds @ [
        PUSH (Id "f");
        PUSH (Val (Z 1));
        MALLOC;
        CALL;
    ] in

    (* Second Call *)
    let cmds = cmds @ [
        PUSH (Id "f");
        PUSH (Val (Z 2));
        MALLOC;
        CALL;
    ] in

    (* Check if allocated memory location's values are not affected by GC() *)
    let cmds = 
      append 126 
        (fun i -> 
          let v = Printf.sprintf "x%d" i in 
            [PUSH (Id v);
            LOAD;
            ADD]
        ) (cmds @ [PUSH (Val (Z 0));]) in 

    let cmds = cmds @ [PUT] in
    cmds

let _ = run cmds8

(*[Value]
"252"

[Test]*)
let cmds9 = 
    let cmds = append 127 (fun _ -> [
        MALLOC;
        BIND "x"; 
        PUSH (Val (Z 100));
        PUSH (Id "x");
        STORE;
        ]
    ) [] in
    
    (* Location on the Stack *)
    let cmds = cmds @ [PUSH (Val (Z 200));MALLOC] in 

    (* Trigger GC *)
    let cmds = cmds @ [MALLOC;POP] in 

    (* Location that was on the stack is used here *)
    let cmds = cmds @ [STORE] in

    (* Access all the allocated memory locations, ensuring they must not have been collected *)
    let cmds = append 127 (fun _ -> [
        PUSH (Id "x");
        LOAD;
        POP;
        
        UNBIND;
        POP;
        ]
    ) cmds in

    cmds

let _ = run cmds9

(*[Exception]
GC_Failure

[Test]*)
let cmds10 = 
    let cmds = append 127 (fun _ -> [
        MALLOC;
        BIND "x"; 
        PUSH (Val (Z 200));
        PUSH (Id "x");
        STORE;
        ]
    ) [] in

    let cmds = cmds @ [
        (* location value on stack : must not be collected, since used below *)
        PUSH (Val (Z 300));
        MALLOC;

        (* Trigger GC *)
        PUSH (Val (Z 400));
        MALLOC;
        STORE;
    
        STORE;
        ] in

    (* Access all the allocated memory locations, ensuring they must not have been collected *)
    let cmds = append 127 (fun _ -> [
        PUSH (Id "x");
        LOAD;
        POP;
        
        UNBIND;
        POP;
        ]
    ) cmds in

    cmds

let _ = run cmds10

(*[Exception]
GC_Failure*)

