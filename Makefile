ROCQ ?= /opt/opam/4.14.3/bin/rocq
OCAMLC ?= /opt/opam/4.14.3/bin/ocamlc
OCAMLDEP ?= /opt/opam/4.14.3/bin/ocamldep
ROCQFLAGS := -q -Q . ''

VFILES := PatriciaBits.v Patricia.v PatriciaProof.v \
	StringBits.v StringPatricia.v StringPatriciaProof.v
VOFILES := $(VFILES:.v=.vo)

.PHONY: all proof extraction ocaml test clean

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

Patricia.vo: PatriciaBits.vo
PatriciaProof.vo: PatriciaBits.vo Patricia.vo
StringPatricia.vo: StringBits.vo
StringPatriciaProof.vo: StringBits.vo StringPatricia.vo

%.vo: %.v
	$(ROCQ) compile $(ROCQFLAGS) $<

clean:
	rm -f *.vo *.vos *.vok *.glob *.aux .*.aux *.lia.cache
	rm -f extracted/*.ml extracted/*.mli extracted/*.cmi extracted/*.cmo
	rm -f PatriciaTest.cmi PatriciaTest.cmo patricia-test
