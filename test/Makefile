.PHONY: check checker

# nproc command prints the number of CPUs.
SHARDS?=`nproc 2> /dev/null || echo 4`

check: checker
	./test_codegen -shards $(SHARDS)

checker: test_codegen

test_codegen: test_codegen.ml
	ocamlfind ocamlopt -package ounit2 -linkpkg str.cmxa test_codegen.ml -o test_codegen

