(* Public testcase 4 : ifzero *)

ifzero ((fn b => b and 1) 0) then 1 else 2

(* Output : 1 in lambda encoding *)
