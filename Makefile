OCB_FLAGS = -use-ocamlfind -pkg unix -pkg yojson -pkg ocamlyices -I util -I input -I logic -I rewriting -I termination

OCB = 		ocamlbuild $(OCB_FLAGS)

all: 		native byte # profile debug
		cp main.byte madmax

clean:
			$(OCB) -clean

native:  	sanity
			$(OCB) main.native

byte: 		sanity
			$(OCB) main.byte

profile: 	sanity
			$(OCB) -tag profile main.native

debug: 		sanity
			$(OCB) -tag debug main.byte

sanity:
			# check that packages can be found
			ocamlfind query yojson
			ocamlfind query ocamlyices

test: 		native
			./main.native -h

.PHONY: 	all clean byte native profile debug sanity test
