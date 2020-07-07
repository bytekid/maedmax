OCB_FLAGS = -use-ocamlfind -cflag -thread \
  -pkg unix -pkg yojson -pkg ocamlyices -pkg xml-light -pkg str -pkg z3 \
	-I src -I src/util -I src/input -I src/logic -I src/proof -I src/rewriting \
	-I src/termination # -pkg z3

OCB = ocamlbuild $(OCB_FLAGS)
OCB_NATIVE = ocamlbuild $(OCB_FLAGS)

all: 		native byte # profile debug
		    cp main.byte maedmax

clean:
			$(OCB) -clean

native:  	sanity
			$(OCB_NATIVE) main.native
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
			ocamlfind query ocamlyices

test: 		native
			./main.native -h

.PHONY: 	all clean byte native profile debug sanity test

starexec:
			cd _build; ocamlfind ocamlopt -thread -linkpkg -package str -package xml-light -package ocamlyices -package yojson -package unix -I src/rewriting -I src/util -I src -I src/logic -I src/termination -I src/proof -I src/input /usr/local/lib/libyices.a src/rewriting/signature.cmx src/util/listx.cmx src/util/formatx.cmx src/rewriting/term.cmx src/rewriting/subst.cmx src/util/listset.cmx src/util/prelude.cmx src/rewriting/rule.cmx src/rewriting/rules.cmx src/rewriting/rewriting.cmx src/rewriting/variant.cmx src/theory.cmx src/fingerprintIndex.cmx src/logic/smt.cmx src/logic/yicesx.cmx src/rewriting/overlap.cmx src/termination/order.cmx src/rewriting/constrained.cmx src/settings.cmx src/rewriter.cmx src/proof/trace.cmx src/literal.cmx src/analytics.cmx src/cache.cmx src/termination/acrpo.cmx src/termination/cfs.cmx src/termination/cfsn.cmx src/termination/dp.cmx src/termination/dg.cmx src/termination/kbo.cmx src/termination/lpo.cmx src/termination/mPol.cmx src/termination/strategy.cmx src/ground.cmx src/logic/smtlib.cmx src/util/hashset.cmx src/narrow.cmx src/nodes.cmx src/overlapper.cmx src/proof/pQGrams.cmx src/proof/selectionTrace.cmx src/select.cmx src/ckb.cmx src/rewriting/aclogic.cmx src/rewriting/acrewriting.cmx src/ckb_AC.cmx src/termination/crpo.cmx src/ckb_constr.cmx src/gcr.cmx src/input/ctrs_parser.cmx src/input/ctrs_lexer.cmx src/input/parser.cmx src/input/lexer.cmx src/input/tptpParser.cmx src/input/tptpLexer.cmx src/input/read.cmx src/instgen_eq.cmx src/instgen.cmx src/proof/cpf.cmx src/proof/tptp.cmx src/termination.cmx src/util/timer.cmx src/main.cmx -o src/main.native
