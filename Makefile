CAMLP4OF := camlp4of
OCAMLDEP := ocamldep -pp $(CAMLP4OF)
OCAMLOPT := ocamlopt -pp $(CAMLP4OF)
OCAMLC   := ocamlc -pp $(CAMLP4OF)

USE_CAMLP4 = yes

SOURCES = \
  timer.mli timer.ml \
  json.mli json.ml \
  statistics.mli statistics.ml \
  listx.mli listx.ml \
  listset.mli listset.ml \
  formatx.mli formatx.ml \
  \
  signature.mli signature.ml \
  term.mli term.ml \
  subst.mli subst.ml \
  rule.mli rule.ml \
  rules.mli rules.ml \
  tplparser.mli tplparser.ml \
  rewriting.mli rewriting.ml \
  overlap.mli overlap.ml \
  variant.mli variant.ml \
  \
  dio.mli dio.ml \
  ac_term.mli ac_term.ml \
  ac_subst.mli ac_subst.ml \
  ac_rewriting.mli ac_rewriting.ml \
  ac_overlap.mli ac_overlap.ml \
  \
  parser.mly  \
  tptpParser.mly \
  lexer.mll \
  tptpLexer.mll \
  read.mli read.ml \
  \
  yicesx.mli yicesx.ml \
  constraint.mli constraint.ml \
  cache.mli cache.ml \
  constraints.mli constraints.ml \
  arith.mli arith.ml \
  lpo.mli lpo.ml \
  kbo.mli kbo.ml \
  cfs.mli cfs.ml \
  cfsn.mli cfsn.ml \
  mPol.mli mPol.ml \
  dp.mli dp.ml \
  dg.mli dg.ml \
  ac_orders.mli ac_orders.ml \
  strategy.mli strategy.ml \
  \
  matrix.mli matrix.ml \
  mi.mli mi.ml \
  \
  ckb.mli ckb.ml \
  ac_ckb.mli ac_ckb.ml \
  main.ml

PACKS = num unix str ocamlyices yojson 

RESULT = maxcompdp

all: nc

install: $(RESULT)
	install -t /usr/local/bin $(RESULT)

archive:
	git archive --format=tar --prefix=maxcomp/ HEAD | gzip > cc-0.1.tar.gz

profile: pbc pnc

include OCamlMakefile
