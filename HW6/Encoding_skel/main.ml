(*
 * SNU 4190.310 Programming Languages 
 *
 * Encoding
 *)

open Encode
open Pp
open M

open Evaluate

let main () =
    let src = ref "" in
    let _ =
        Arg.parse
          []
          (fun x -> src := x)
          ("Usage: " ^ (Filename.basename Sys.argv.(0)) ^ " [-ptree] [file]")
    in
	let lexbuf = Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let pgm = Parser.program Lexer.start lexbuf in
	
	print_string "=============\n";
	print_string "input program\n";
	print_string "=============\n";
	M_Printer.print pgm;
	print_string "\n\n\n============\n";
	print_string "output program\n";
	print_string "=============\n";
	let output = Encoder.encode pgm in 
	Pp.pp (output);
	print_string "\n\n\n============\n"; 
	print_string "reduced program\n"; 
   	print_string "=============\n"; 
   	Pp.pp (Evaluator.reduce output); 
   	print_string "\n"

let _ = main ()
