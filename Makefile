ppx_indexop:ppx_indexop.native
	mv ppx_indexop.native ppx_indexop

all: ppx_indexop.native tests/test.native

ppx_indexop.native:ppx_indexop.ml
	ocamlbuild -pkg compiler-libs.common ppx_indexop.native

tests/test.native:
	ocamlbuild -cflags -ppx,"ppx_indexop"  tests/test.native
