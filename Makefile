# Builds the command-line interpreter, mu, and the browser workspace,
# workspace.js, which index.html loads. Intermediate files go in _build.

all: mu workspace.js

mu: _build/bootstrap.cmx _build/main.cmx
	ocamlfind ocamlopt $^ -o $@

workspace.js: _build/bootstrap.cmo _build/workspace.cmo
	ocamlfind ocamlc $(PACKAGES) -linkpkg $^ -o _build/workspace.byte
	js_of_ocaml _build/workspace.byte -o $@

_build/main.cmx: _build/bootstrap.cmx
_build/workspace.cmo: _build/bootstrap.cmo
workspace.js _build/workspace.cmo: PACKAGES = -package js_of_ocaml,js_of_ocaml-ppx

_build/%.cmx: %.ml | _build
	ocamlfind ocamlopt -I _build -c $< -o $@

_build/%.cmo: %.ml | _build
	ocamlfind ocamlc $(PACKAGES) -I _build -c $< -o $@

_build:
	mkdir -p $@

test: mu
	scripts/test.sh

clean:
	rm -rf _build mu workspace.js

.PHONY: all test clean
