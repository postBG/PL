all: run

run: lexer.cmo parser.cmo m0.cmo cps.cmo main.cmo
	ocamlc -o run lexer.cmo parser.cmo m0.cmo cps.cmo pp.cmo main.cmo

m0.cmo : m0.ml 
	ocamlc -c m0.ml

pp.cmo : pp.ml m0.cmo
	ocamlc -c pp.ml

cps.cmo : cps.ml m0.cmo
	ocamlc -c cps.ml

parser.ml: parser.mly m0.cmo 
	ocamlyacc parser.mly

parser.mli: parser.mly
	ocamlyacc parser.mly

parser.cmi: parser.mli
	ocamlc -c parser.mli

parser.cmo: parser.ml parser.cmi
	ocamlc -c parser.ml

main.cmo : main.ml m0.cmo cps.cmo pp.cmo
	ocamlc -c main.ml

lexer.cmo: lexer.ml
	ocamlc -c lexer.ml

lexer.ml: lexer.mll parser.cmo
	ocamllex lexer.mll

clean:
	rm -f *.cmo *.cmi *.cmx  parser.mli parser.ml lexer.ml run *.o
