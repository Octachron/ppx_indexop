CCX=ocamlc -ppx "../ppx_indexop.native"

all: ppx_indexop.native tests/test

ppx_indexop.native:ppx_indexop.ml
	ocamlbuild -pkg compiler-libs.common ppx_indexop.native

tests/test.cmi : tests/test.mli
	cd tests && ${CCX} test.mli && cd ..

tests/test: tests/test.ml ppx_indexop.native tests/test.cmi
	cd tests && ${CCX} test.ml -o test && cd ..

