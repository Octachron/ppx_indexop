all: ppx_indexop.native test

ppx_indexop.native:ppx_indexop.ml
	ocamlbuild -pkg compiler-libs.common ppx_indexop.native
test: test.ml ppx_indexop.native
	ocamlc -ppx "./ppx_indexop.native" test.ml -o test && rm test.cm{o,i}

