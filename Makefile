OCB_FLAGS = -use-ocamlfind -cflag -thread \
  -pkg unix -pkg yojson -pkg z3 -pkg xml-light -pkg str \
	-I src -I src/util -I src/input -I src/logic -I src/proof -I src/rewriting \
	-I src/termination #  -pkg ocamlyices

OCB = 		ocamlbuild $(OCB_FLAGS)

all: 		native byte # profile debug
		    cp main.byte maedmax

clean:
			$(OCB) -clean

native:  	sanity
			$(OCB) main.native
			cp main.native maedmax

byte: 		sanity
			$(OCB) main.byte

profile: 	sanity
			$(OCB) -tag profile main.native

debug: 		sanity
			$(OCB) -tag debug main.byte

sanity:
			# check that packages can be found
			ocamlfind query yojson
			ocamlfind query z3
			#ocamlfind query ocamlyices

test: 		native
			./main.native -h

.PHONY: 	all clean byte native profile debug sanity test
