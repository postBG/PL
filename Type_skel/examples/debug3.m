(* Polymorphism with WRITE *)

let val print = fn x => 
  (write x; true)
in
  print 1
end

(* Reseult : (bool, (bool, bool)) *)
