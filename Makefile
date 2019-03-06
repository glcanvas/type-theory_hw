all:
	ocamllex ./parser/lexer.mll
	ocamlyacc ./parser/parser.mly
	mv ./parser/lexer.ml ./lexer.ml
	mv ./parser/parser.ml ./parser.ml
	mv ./parser/parser.mli ./parser.mli
	ocamlc tree.ml parser.mli parser.ml lexer.ml c.ml -o rn.out

run:
	./rn.out

pack:
	zip task1 Makefile *.ml ./parser/*
