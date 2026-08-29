ROCQ ?= /opt/opam/4.14.3/bin/rocq
OCAMLC ?= /opt/opam/4.14.3/bin/ocamlc
OCAMLOPT ?= /opt/opam/4.14.3/bin/ocamlopt
OCAMLDEP ?= /opt/opam/4.14.3/bin/ocamldep
ROCQFLAGS := -q -Q . ''

VFILES := PatriciaBits.v Patricia.v PatriciaProof.v \
	StringBits.v StringPatricia.v StringPatriciaProof.v
VOFILES := $(VFILES:.v=.vo)
PUBLIC_INTERFACES := PatriciaMap.mli StringPatriciaMap.mli
PUBLIC_IMPLEMENTATIONS := PatriciaMap.ml StringPatriciaMap.ml
PUBLIC_CMOS := PatriciaMap.cmo StringPatriciaMap.cmo
PUBLIC_CMXS := PatriciaMap.cmx StringPatriciaMap.cmx

.PHONY: all proof extraction ocaml test benchmark clean

all: proof extraction ocaml test

proof: $(VOFILES)

extraction: proof
	@mkdir -p extracted
	$(ROCQ) compile $(ROCQFLAGS) PatriciaExtract.v
	mv extracted/Patricia.ml extracted/PatriciaInternal.ml
	mv extracted/Patricia.mli extracted/PatriciaInternal.mli
	mv extracted/StringPatricia.ml extracted/StringPatriciaInternal.ml
	mv extracted/StringPatricia.mli extracted/StringPatriciaInternal.mli
	$(RM) extracted/Patricia.cmi extracted/Patricia.cmo extracted/Patricia.cmx extracted/Patricia.o
	$(RM) extracted/StringPatricia.cmi extracted/StringPatricia.cmo \
	  extracted/StringPatricia.cmx extracted/StringPatricia.o

ocaml: extraction $(PUBLIC_INTERFACES) $(PUBLIC_IMPLEMENTATIONS)
	cd extracted && $(OCAMLDEP) -sort *.mli *.ml | xargs $(OCAMLC) -c
	$(OCAMLC) -I extracted -c $(PUBLIC_INTERFACES) $(PUBLIC_IMPLEMENTATIONS)

test: ocaml PatriciaTest.ml
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmo/g'` && \
	  $(OCAMLC) -I . -I .. -o ../patricia-test $$objects \
	    $(addprefix ../,$(PUBLIC_CMOS)) ../PatriciaTest.ml
	./patricia-test

# Native code is deliberate here: this target compares runtime and allocation
# characteristics, while the regular oracle test remains a quick bytecode test.
benchmark: ocaml PatriciaBenchmark.ml
	cd extracted && $(OCAMLOPT) -c `$(OCAMLDEP) -sort *.ml`
	$(OCAMLOPT) -I extracted -c $(PUBLIC_IMPLEMENTATIONS)
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmx/g'` && \
	  $(OCAMLOPT) -I . -I .. unix.cmxa -o ../patricia-benchmark $$objects \
	    $(addprefix ../,$(PUBLIC_CMXS)) ../PatriciaBenchmark.ml
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
	rm -f PatriciaMap.cmi PatriciaMap.cmo PatriciaMap.cmx PatriciaMap.o
	rm -f StringPatriciaMap.cmi StringPatriciaMap.cmo StringPatriciaMap.cmx StringPatriciaMap.o
	rm -f PatriciaTest.cmi PatriciaTest.cmo PatriciaBenchmark.cmi PatriciaBenchmark.cmx PatriciaBenchmark.o
	rm -f patricia-test patricia-benchmark
