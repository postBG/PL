(* Polymorphism with WRITE *)

let val print = fn x => 
  (write x; true)
in
  print (fn x => x)
end

(* Reseult : (bool, (bool, bool)) *)
