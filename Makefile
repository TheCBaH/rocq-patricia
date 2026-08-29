ROCQ ?= /opt/opam/4.14.3/bin/rocq
OCAMLC ?= /opt/opam/4.14.3/bin/ocamlc
OCAMLOPT ?= /opt/opam/4.14.3/bin/ocamlopt
OCAMLDEP ?= /opt/opam/4.14.3/bin/ocamldep
ROCQFLAGS := -q -Q . ''

VFILES := PatriciaBits.v Patricia.v PatriciaProof.v \
	StringBits.v NativeRefinement.v StringPatricia.v StringPatriciaProof.v
VOFILES := $(VFILES:.v=.vo)
PUBLIC_INTERFACES := PatriciaMap.mli StringPatriciaMap.mli
PUBLIC_IMPLEMENTATIONS := PatriciaMap.ml StringPatriciaMap.ml
PUBLIC_CMOS := PatriciaMap.cmo StringPatriciaMap.cmo
PUBLIC_CMXS := PatriciaMap.cmx StringPatriciaMap.cmx
REFERENCE_DIR := reference_extracted
REFERENCE_PACK := PatriciaReference.cmo

.PHONY: all proof assumptions extraction reference-extraction ocaml \
	reference-ocaml test differential benchmark clean

all: proof assumptions extraction reference-extraction ocaml reference-ocaml \
	test differential

proof: $(VOFILES)

assumptions: proof check-assumptions.sh
	sh ./check-assumptions.sh $(ROCQ) $(ROCQFLAGS)

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

# This second extraction deliberately omits every Patricia-specific custom
# realizer. Its generated modules are later packed into one namespace so they
# can be linked beside the optimized extraction for direct differential tests.
reference-extraction: proof PatriciaReferenceExtract.v
	@mkdir -p $(REFERENCE_DIR)
	$(ROCQ) compile $(ROCQFLAGS) PatriciaReferenceExtract.v
	$(RM) $(REFERENCE_DIR)/String.cmi $(REFERENCE_DIR)/String.cmo \
	  $(REFERENCE_DIR)/String.cmx $(REFERENCE_DIR)/String.o

ocaml: extraction $(PUBLIC_INTERFACES) $(PUBLIC_IMPLEMENTATIONS)
	cd extracted && $(OCAMLDEP) -sort *.mli *.ml | xargs $(OCAMLC) -c
	$(OCAMLC) -I extracted -c $(PUBLIC_INTERFACES) $(PUBLIC_IMPLEMENTATIONS)

reference-ocaml: reference-extraction
	# Separate extraction emits an empty [String] unit which would shadow
	# [Stdlib.String] used by the native-string eliminator; it is not linked.
	cd $(REFERENCE_DIR) && \
	  sources=`find . -maxdepth 1 -type f \( -name '*.mli' -o -name '*.ml' \) \
	    ! -name 'String.mli' ! -name 'String.ml' -printf '%f '` && \
	  $(OCAMLDEP) -sort $$sources | xargs $(OCAMLC) -c && \
	  ml_sources=`find . -maxdepth 1 -type f -name '*.ml' \
	    ! -name 'String.ml' -printf '%f '` && \
	  objects=`$(OCAMLDEP) -sort $$ml_sources | sed 's/\.ml/.cmo/g'` && \
	  $(OCAMLC) -pack -o ../$(REFERENCE_PACK) $$objects

test: ocaml PatriciaTest.ml
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmo/g'` && \
	  $(OCAMLC) -I . -I .. -o ../patricia-test $$objects \
	    $(addprefix ../,$(PUBLIC_CMOS)) ../PatriciaTest.ml
	./patricia-test

differential: ocaml reference-ocaml PatriciaDifferentialTest.ml
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmo/g'` && \
	  $(OCAMLC) -I . -I .. -o ../patricia-differential-test $$objects \
	    ../$(REFERENCE_PACK) ../PatriciaDifferentialTest.ml
	./patricia-differential-test

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
NativeRefinement.vo: PatriciaBits.vo StringBits.vo
StringPatriciaProof.vo: StringBits.vo StringPatricia.vo

%.vo: %.v
	$(ROCQ) compile $(ROCQFLAGS) $<

clean:
	rm -f *.vo *.vos *.vok *.glob *.aux .*.aux *.lia.cache
	rm -f extracted/*.ml extracted/*.mli extracted/*.cmi extracted/*.cmo extracted/*.cmx extracted/*.o
	rm -f $(REFERENCE_DIR)/*.ml $(REFERENCE_DIR)/*.mli $(REFERENCE_DIR)/*.cmi \
	  $(REFERENCE_DIR)/*.cmo $(REFERENCE_DIR)/*.cmx $(REFERENCE_DIR)/*.o
	rm -f PatriciaMap.cmi PatriciaMap.cmo PatriciaMap.cmx PatriciaMap.o
	rm -f StringPatriciaMap.cmi StringPatriciaMap.cmo StringPatriciaMap.cmx StringPatriciaMap.o
	rm -f PatriciaReference.cmi PatriciaReference.cmo
	rm -f PatriciaTest.cmi PatriciaTest.cmo PatriciaDifferentialTest.cmi \
	  PatriciaDifferentialTest.cmo PatriciaBenchmark.cmi PatriciaBenchmark.cmx \
	  PatriciaBenchmark.o
	rm -f patricia-test patricia-differential-test patricia-benchmark
