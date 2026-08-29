ROCQ ?= /opt/opam/4.14.3/bin/rocq
OCAMLC ?= /opt/opam/4.14.3/bin/ocamlc
OCAMLOPT ?= /opt/opam/4.14.3/bin/ocamlopt
OCAMLDEP ?= /opt/opam/4.14.3/bin/ocamldep
ROCQFLAGS := -q -Q . ''

VFILES := PatriciaBits.v Patricia.v PatriciaProof.v \
	StringBits.v StringPatricia.v StringPatriciaProof.v
VOFILES := $(VFILES:.v=.vo)

.PHONY: all proof extraction ocaml test benchmark clean

all: proof extraction ocaml test

proof: $(VOFILES)

extraction: proof
	@mkdir -p extracted
	$(ROCQ) compile $(ROCQFLAGS) PatriciaExtract.v

ocaml: extraction
	cd extracted && $(OCAMLDEP) -sort *.mli *.ml | xargs $(OCAMLC) -c

test: ocaml PatriciaTest.ml
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmo/g'` && \
	  $(OCAMLC) -I . -o ../patricia-test $$objects ../PatriciaTest.ml
	./patricia-test

# Native code is deliberate here: this target compares runtime and allocation
# characteristics, while the regular oracle test remains a quick bytecode test.
benchmark: ocaml PatriciaBenchmark.ml
	cd extracted && $(OCAMLOPT) -c `$(OCAMLDEP) -sort *.ml`
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmx/g'` && \
	  $(OCAMLOPT) -I . unix.cmxa -o ../patricia-benchmark $$objects ../PatriciaBenchmark.ml
	./patricia-benchmark

Patricia.vo: PatriciaBits.vo
PatriciaProof.vo: PatriciaBits.vo Patricia.vo
StringPatricia.vo: StringBits.vo
StringPatriciaProof.vo: StringBits.vo StringPatricia.vo

%.vo: %.v
	$(ROCQ) compile $(ROCQFLAGS) $<

clean:
	rm -f *.vo *.vos *.vok *.glob *.aux .*.aux *.lia.cache
	rm -f extracted/*.ml extracted/*.mli extracted/*.cmi extracted/*.cmo extracted/*.cmx extracted/*.o
	rm -f PatriciaTest.cmi PatriciaTest.cmo PatriciaBenchmark.cmi PatriciaBenchmark.cmx PatriciaBenchmark.o
	rm -f patricia-test patricia-benchmark
