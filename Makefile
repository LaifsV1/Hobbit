MAIN=hobbit

compile:
	ocamlbuild -I src/parser -I src/up-to-techniques -I src -use-ocamlfind -tag thread -package z3 -use-menhir src/hobbit.native

clean:
	ocamlbuild -clean
	rm -f parser.{ml,mli} lexer.ml

show-branches:
	git log --oneline --decorate --graph --all
