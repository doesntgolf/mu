# Builds the command-line interpreter, mu, and the browser workspace,
# workspace.js, which index.html loads. Intermediate files go in _build, in
# separate directories for native code and bytecode, since each compiler
# writes its own .cmi files.

all: mu workspace.js

mu: _build/native/bootstrap.cmx _build/native/prelude.cmx _build/native/main.cmx
	ocamlfind ocamlopt $^ -o $@

workspace.js: _build/byte/bootstrap.cmo _build/byte/prelude.cmo _build/byte/workspace.cmo
	ocamlfind ocamlc $(PACKAGES) -linkpkg $^ -o _build/byte/workspace.byte
	js_of_ocaml _build/byte/workspace.byte -o $@

_build/native/main.cmx: _build/native/bootstrap.cmx _build/native/prelude.cmx
_build/byte/workspace.cmo: _build/byte/bootstrap.cmo _build/byte/prelude.cmo
workspace.js _build/byte/workspace.cmo: PACKAGES = -package js_of_ocaml,js_of_ocaml-ppx

_build/native/%.cmx: %.ml | _build/native
	ocamlfind ocamlopt -I _build/native -c $< -o $@

_build/byte/%.cmo: %.ml | _build/byte
	ocamlfind ocamlc $(PACKAGES) -I _build/byte -c $< -o $@

_build/native _build/byte:
	mkdir -p $@

test: mu
	scripts/test.sh

clean:
	rm -rf _build mu workspace.js

.PHONY: all test clean
