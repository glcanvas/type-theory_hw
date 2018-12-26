ocamldep -modules a.ml > a.ml.depends
ocamlc -c -o a.cmo a.ml
ocamlopt -c -o a.cmx a.ml
ocamlopt tree.cmx parser.cmx lexer.cmx a.cmx -o a.native