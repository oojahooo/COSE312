all: run

run: enum.cmo pMap.cmo lexer.cmo parser.cmo s.cmo t.cmo translator_2018320190.cmo optimizer_2018320190.cmo main.cmo
		ocamlc -o run enum.cmo pMap.cmo lexer.cmo parser.cmo s.cmo t.cmo translator_2018320190.cmo optimizer_2018320190.cmo main.cmo

enum.cmo : enum.ml
		ocamlc -c enum.ml

pMap.cmo : enum.cmo pMap.ml
		ocamlc -c pMap.ml

s.cmo : s.ml
		ocamlc -c s.ml

t.cmo : pMap.cmo t.ml
		ocamlc -c t.ml

translator_2018320190.cmo : s.cmo t.cmo translator_2018320190.ml
		ocamlc -c translator_2018320190.ml

optimizer_2018320190.cmo : t.cmo
		ocamlc -c optimizer_2018320190.ml

parser.ml: parser.mly s.cmo
		ocamlyacc parser.mly

parser.mli: parser.mly
		ocamlyacc parser.mly

parser.cmi: parser.mli
		ocamlc -c parser.mli

parser.cmo: parser.ml parser.cmi
		ocamlc -c parser.ml

main.cmo : s.cmo t.cmo translator_2018320190.cmo optimizer_2018320190.cmo main.ml
		ocamlc -c main.ml

lexer.cmo: lexer.ml
		ocamlc -c lexer.ml

lexer.ml: lexer.mll parser.cmo
		ocamllex lexer.mll

clean:
		rm -f *.cmx *.cmi parser.mli parser.ml lexer.ml run *.o *.cmo
