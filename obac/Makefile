
# NOTE : if your projet uses extra OCaml libraries, you might
# want to add option -use-ocamlfind to ocamlbuild below
# and indicate these extra libraries in the file _tags

all:
	ocamlbuild -use-ocamlfind main.native

byte:
	ocamlbuild -tag debug main.byte

clean:
	ocamlbuild -clean
