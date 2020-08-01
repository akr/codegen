.PHONY: check checker

SHARDS?=4

check: checker
	./test_codegen -shards $(SHARDS)

checker: test_codegen

test_codegen: test_codegen.ml
	ocamlfind ocamlopt -package ounit2 -linkpkg str.cmxa test_codegen.ml -o test_codegen

