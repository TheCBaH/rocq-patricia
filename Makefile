ROCQ ?= /opt/opam/4.14.3/bin/rocq
OCAMLC ?= /opt/opam/4.14.3/bin/ocamlc
OCAMLOPT ?= /opt/opam/4.14.3/bin/ocamlopt
OCAMLDEP ?= /opt/opam/4.14.3/bin/ocamldep
ROCQFLAGS := -q -Q . ''

CORE_VFILES := PatriciaBits.v Patricia.v PatriciaProof.v \
	StringBits.v NativeRefinement.v NativeStringWorker.v StringPatricia.v StringPatriciaProof.v
UNION_VFILES := PatriciaUnion.v PatriciaUnionProof.v \
	StringPatriciaUnion.v StringPatriciaUnionProof.v NativeHeapRefinement.v
VFILES := $(CORE_VFILES) $(UNION_VFILES)
VOFILES := $(VFILES:.v=.vo)
CORE_VOFILES := $(CORE_VFILES:.v=.vo)
UNION_VOFILES := $(UNION_VFILES:.v=.vo)
PUBLIC_INTERFACES := PatriciaMap.mli StringPatriciaMap.mli
PUBLIC_IMPLEMENTATIONS := PatriciaMap.ml StringPatriciaMap.ml
PUBLIC_CMOS := PatriciaMap.cmo StringPatriciaMap.cmo
PUBLIC_CMXS := PatriciaMap.cmx StringPatriciaMap.cmx
REFERENCE_DIR := reference_extracted
REFERENCE_PACK := PatriciaReference.cmo
HASHTABLE_VFILES := HashTableSpec.v HashTableBits.v HashTableBucket.v HashTable.v HashTableProof.v HashTableNative.v HashTableSkeleton.v
HASHTABLE_VOFILES := $(HASHTABLE_VFILES:.v=.vo)

.PHONY: all proof core-proof union-proof assumptions extraction extraction-boundary native-string-worker-audit \
	native-union-realizer-audit ocaml-physical-equality-audit \
	cached-representative-audit \
	reference-extraction ocaml reference-ocaml test union-oracle union-oracle-native differential \
	benchmark benchmark-smoke union-profile map-filter-profile remove-profile reference-profile compiler-config clean

.PHONY: hashtable hashtable-proof hashtable-skeleton-extraction hashtable-reference hashtable-reference-ocaml hashtable-reference-test hashtable-wrapper-test hashtable-wrapper-test-native hashtable-native-primitives-test hashtable-extraction-audit hashtable-assumptions

.PHONY: string-primitive-profile
.PHONY: string-worker-performance

.PHONY: set-profile

.PHONY: map-filter-profile

.PHONY: remove-profile

all: proof assumptions extraction extraction-boundary native-string-worker-audit native-union-realizer-audit \
	cached-representative-audit \
	reference-extraction ocaml reference-ocaml \
	test union-oracle differential

string-worker-performance:
	sh ./check-string-worker-performance.sh

proof: $(VOFILES)

core-proof: $(CORE_VOFILES)

# Fast iteration boundary for the experimental specialized-union workers and
# certificates.  Established map proofs are reused through their cached .vo
# files and are rebuilt only when their own sources changed.
union-proof: $(UNION_VOFILES)

# H0 is intentionally separate from the established Patricia build.  Later
# gates extend these targets without making the two extraction namespaces
# collide.
hashtable: hashtable-proof hashtable-assumptions hashtable-extraction-audit \
	hashtable-reference-test hashtable-wrapper-test hashtable-wrapper-test-native \
	hashtable-native-primitives-test

hashtable-proof: $(HASHTABLE_VOFILES)

hashtable-skeleton-extraction: hashtable-proof HashTableSkeletonExtract.v
	@mkdir -p hashtable_skeleton_extracted
	$(RM) hashtable_skeleton_extracted/*.ml hashtable_skeleton_extracted/*.mli \
	  hashtable_skeleton_extracted/*.cmi hashtable_skeleton_extracted/*.cmo \
	  hashtable_skeleton_extracted/*.cmx hashtable_skeleton_extracted/*.o
	$(ROCQ) compile $(ROCQFLAGS) HashTableSkeletonExtract.v

hashtable-reference: hashtable-proof HashTableReferenceExtract.v
	@mkdir -p hashtable_reference_extracted
	$(RM) hashtable_reference_extracted/*.ml hashtable_reference_extracted/*.mli \
	  hashtable_reference_extracted/*.cmi hashtable_reference_extracted/*.cmo \
	  hashtable_reference_extracted/*.cmx hashtable_reference_extracted/*.o
	$(ROCQ) compile $(ROCQFLAGS) HashTableReferenceExtract.v
	cd hashtable_reference_extracted && $(OCAMLDEP) -sort *.mli *.ml | xargs $(OCAMLC) -c

hashtable-reference-ocaml: hashtable-reference HashMap.mli HashMap.ml
	$(OCAMLC) -I hashtable_reference_extracted -c HashMap.mli HashMap.ml

hashtable-reference-test: hashtable-reference HashTableReferenceTest.ml
	cd hashtable_reference_extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmo/g'` && \
	  $(OCAMLC) -I . -I .. -o ../hashtable-reference-test $$objects ../HashTableReferenceTest.ml
	./hashtable-reference-test

hashtable-wrapper-test: hashtable-reference-ocaml HashMapTest.ml
	cd hashtable_reference_extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmo/g'` && \
	  $(OCAMLC) -I . -I .. -o ../hashtable-wrapper-test $$objects ../HashMap.cmo ../HashMapTest.ml
	./hashtable-wrapper-test

hashtable-wrapper-test-native: hashtable-reference HashMap.mli HashMap.ml HashMapTest.ml
	cd hashtable_reference_extracted && $(OCAMLDEP) -sort *.mli *.ml | xargs $(OCAMLOPT) -c
	$(OCAMLOPT) -I hashtable_reference_extracted -c HashMap.mli HashMap.ml
	cd hashtable_reference_extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmx/g'` && \
	  $(OCAMLOPT) -I . -I .. -o ../hashtable-wrapper-native-test $$objects ../HashMap.cmx ../HashMapTest.ml
	./hashtable-wrapper-native-test

hashtable-extraction-audit: HashMap.mli HashMap.ml check-hashtable-extraction-boundary.sh
	sh ./check-hashtable-extraction-boundary.sh HashMap.mli HashMap.ml

hashtable-native-primitives-test: HashTablePrimitives.mli HashTablePrimitives.ml HashTablePrimitivesTest.ml
	$(OCAMLOPT) -c HashTablePrimitives.mli HashTablePrimitives.ml HashTablePrimitivesTest.ml
	$(OCAMLOPT) -o hashtable-native-primitives-test HashTablePrimitives.cmx HashTablePrimitivesTest.cmx
	./hashtable-native-primitives-test

hashtable-assumptions: hashtable-proof check-hashtable-assumptions.sh
	sh ./check-hashtable-assumptions.sh $(ROCQ) $(ROCQFLAGS)

assumptions: proof check-assumptions.sh
	sh ./check-assumptions.sh $(ROCQ) $(ROCQFLAGS)

extraction-boundary: PatriciaExtract.v check-extraction-boundary.sh
	sh ./check-extraction-boundary.sh PatriciaExtract.v

native-string-worker-audit: extraction check-native-string-workers.sh
	sh ./check-native-string-workers.sh PatriciaExtract.v extracted/NativeStringWorker.ml

# Check the source-extracted proof-guided workers remain direct recursion with
# no operational size/fuel argument or nested recursive closure.
native-union-realizer-audit: extraction check-native-union-realizers.sh
	sh ./check-native-union-realizers.sh extracted/PatriciaUnion.ml \
	  extracted/StringPatriciaUnion.ml

cached-representative-audit: extraction check-cached-representative-consumers.sh
	sh ./check-cached-representative-consumers.sh extracted/StringPatriciaInternal.ml \
	  extracted/StringPatriciaUnion.ml PatriciaExtract.v

# Optional implementation audit for the selected OCaml compiler sources. It
# intentionally stays outside the normal proof/correctness gate: a source scan
# is evidence about one toolchain, not a compiler-correctness theorem.
OCAML_SOURCE_ROOT ?= /opt/opam/4.14.3/.opam-switch/sources/ocaml-base-compiler.4.14.3

ocaml-physical-equality-audit: check-ocaml-physical-equality.sh
	sh ./check-ocaml-physical-equality.sh $(OCAML_SOURCE_ROOT)

extraction: proof
	@mkdir -p extracted
	$(ROCQ) compile $(ROCQFLAGS) PatriciaExtract.v
	mv extracted/Patricia.ml extracted/PatriciaInternal.ml
	mv extracted/Patricia.mli extracted/PatriciaInternal.mli
	mv extracted/StringPatricia.ml extracted/StringPatriciaInternal.ml
	mv extracted/StringPatricia.mli extracted/StringPatriciaInternal.mli
	sed -i 's/^open Patricia$$/open PatriciaInternal/' \
	  extracted/PatriciaUnion.ml extracted/PatriciaUnion.mli
	sed -i 's/^open StringPatricia$$/open StringPatriciaInternal/' \
	  extracted/StringPatriciaUnion.ml extracted/StringPatriciaUnion.mli
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

union-oracle: ocaml PatriciaUnionTest.ml
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmo/g'` && \
	  $(OCAMLC) -I . -I .. -o ../patricia-union-test $$objects \
	    ../PatriciaUnionTest.ml
	./patricia-union-test

# The default union oracle uses bytecode for speed.  This companion target
# exercises the same structural, semantic, mutable-payload, and physical-root
# checks through the native code path used by the public performance backend.
# It is finite runtime evidence for the [(==)] refinement boundary, not a
# compiler or heap-correctness proof.
union-oracle-native: extraction PatriciaUnionTest.ml
	cd extracted && $(OCAMLDEP) -sort *.mli *.ml | xargs $(OCAMLOPT) -c
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmx/g'` && \
	  $(OCAMLOPT) -I . -I .. -o ../patricia-union-native-test $$objects \
	    ../PatriciaUnionTest.ml
	./patricia-union-native-test

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

# This is deliberately separate from [benchmark]: it compares the established
# nested changed-result union with the selected closure-free fuel worker
# through their generated implementation modules.
union-profile: extraction PatriciaUnionProfile.ml
	cd extracted && $(OCAMLDEP) -sort *.mli *.ml | xargs $(OCAMLOPT) -c
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmx/g'` && \
	  $(OCAMLOPT) -I . -I .. unix.cmxa -o ../patricia-union-profile $$objects \
	    ../PatriciaUnionProfile.ml
	./patricia-union-profile

# Compare the public source-extracted string setter with the one-descent
# experiments and the separately named ordinary two-descent baseline.
set-profile: extraction PatriciaSetProfile.ml
	cd extracted && $(OCAMLDEP) -sort *.mli *.ml | xargs $(OCAMLOPT) -c
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmx/g'` && \
	  $(OCAMLOPT) -I . -I .. unix.cmxa -o ../patricia-set-profile $$objects \
	    ../PatriciaSetProfile.ml
	./patricia-set-profile

map-filter-profile: extraction PatriciaMapFilterProfile.ml StringPatriciaMap.ml
	cd extracted && $(OCAMLDEP) -sort *.mli *.ml | xargs $(OCAMLOPT) -c
	rm -f StringPatriciaMap.cmi StringPatriciaMap.cmx StringPatriciaMap.o \
	  PatriciaMapFilterProfile.cmi PatriciaMapFilterProfile.cmx PatriciaMapFilterProfile.o
	$(OCAMLOPT) -I extracted -c StringPatriciaMap.mli StringPatriciaMap.ml \
	  PatriciaMapFilterProfile.ml
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmx/g'` && \
	  $(OCAMLOPT) -I . -I .. unix.cmxa -o ../patricia-map-filter-profile $$objects \
	  ../StringPatriciaMap.cmx ../PatriciaMapFilterProfile.cmx
	./patricia-map-filter-profile

remove-profile: extraction PatriciaRemoveProfile.ml StringPatriciaMap.ml
	cd extracted && $(OCAMLDEP) -sort *.mli *.ml | xargs $(OCAMLOPT) -c
	rm -f StringPatriciaMap.cmi StringPatriciaMap.cmx StringPatriciaMap.o \
	  PatriciaRemoveProfile.cmi PatriciaRemoveProfile.cmx PatriciaRemoveProfile.o
	$(OCAMLOPT) -I extracted -c StringPatriciaMap.mli StringPatriciaMap.ml \
	  PatriciaRemoveProfile.ml
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmx/g'` && \
	  $(OCAMLOPT) -I . -I .. unix.cmxa -o ../patricia-remove-profile $$objects \
	  ../StringPatriciaMap.cmx ../PatriciaRemoveProfile.cmx
	./patricia-remove-profile

# The proof-aligned extraction has deliberately separate module names from the
# optimized backend.  Keep its native performance profile in a separate binary
# so the normal supported-wrapper benchmark stays focused on its public API.
reference-profile: reference-extraction PatriciaReferenceProfile.ml
	cd $(REFERENCE_DIR) && \
	  sources=`find . -maxdepth 1 -type f \( -name '*.mli' -o -name '*.ml' \) \
	    ! -name 'String.mli' ! -name 'String.ml' -printf '%f '` && \
	  $(OCAMLDEP) -sort $$sources | xargs $(OCAMLOPT) -c
	cd $(REFERENCE_DIR) && \
	  ml_sources=`find . -maxdepth 1 -type f -name '*.ml' \
	    ! -name 'String.ml' -printf '%f '` && \
	  objects=`$(OCAMLDEP) -sort $$ml_sources | sed 's/\.ml/.cmx/g'` && \
	  $(OCAMLOPT) -I . unix.cmxa -o ../patricia-reference-profile $$objects \
	    ../PatriciaReferenceProfile.ml
	./patricia-reference-profile

# This is the primitive-level counterpart of [reference-profile].  It keeps
# all strings and packed/logical position conversion outside timed regions,
# checks the selected native bodies against the proof-aligned extraction, and
# reports a median plus range and allocated words for each batch.  A future
# proved worker can be added as another column without changing the workload
# generator or correctness oracle.
string-primitive-profile: extraction reference-extraction StringPrimitiveProfile.ml benchmarks/StringBitsBaseline.ml
	cd extracted && $(OCAMLDEP) -sort *.mli *.ml | xargs $(OCAMLOPT) -c
	cd $(REFERENCE_DIR) && \
	  sources=`find . -maxdepth 1 -type f \( -name '*.mli' -o -name '*.ml' \) \
	    ! -name 'String.mli' ! -name 'String.ml' -printf '%f '` && \
	  $(OCAMLDEP) -sort $$sources | xargs $(OCAMLOPT) -for-pack PatriciaReference -c && \
	  ml_sources=`find . -maxdepth 1 -type f -name '*.ml' \
	    ! -name 'String.ml' -printf '%f '` && \
	  objects=`$(OCAMLDEP) -sort $$ml_sources | sed 's/\.ml/.cmx/g'` && \
	  $(OCAMLOPT) -pack -o ../PatriciaReference.cmx $$objects
	$(OCAMLOPT) -c benchmarks/StringBitsBaseline.ml
	$(OCAMLOPT) -I extracted -I benchmarks -c StringPrimitiveProfile.ml
	cd extracted && objects=`$(OCAMLDEP) -sort *.ml | sed 's/\.ml/.cmx/g'` && \
	  $(OCAMLOPT) -I . -I .. unix.cmxa -o ../patricia-string-primitive-profile \
	  $$objects ../$(REFERENCE_PACK:.cmo=.cmx) ../benchmarks/StringBitsBaseline.cmx ../StringPrimitiveProfile.cmx
	./patricia-string-primitive-profile

# Record the native compiler settings beside any comparable benchmark series.
# CI pins the OCaml version; this target captures target-dependent details
# such as architecture, word size, Flambda, and the C compiler flags.
compiler-config:
	$(OCAMLOPT) -version
	$(OCAMLOPT) -config | sed -n \
	  -e '/^architecture:/p' -e '/^model:/p' -e '/^system:/p' \
	  -e '/^word_size:/p' -e '/^flambda:/p' -e '/^safe_string:/p' \
	  -e '/^native_c_compiler:/p'

# Small checked workload for CI.  It exercises every benchmark operation but
# neither records the timings nor treats them as performance thresholds.
benchmark-smoke: benchmark

benchmark-smoke: export PATRICIA_BENCH_SIZE := 100
benchmark-smoke: export PATRICIA_BENCH_STRING_LENGTHS := 2
benchmark-smoke: export PATRICIA_BENCH_VARIABLE_STRING_MAX_LENGTH := 2

Patricia.vo: PatriciaBits.vo
PatriciaProof.vo: PatriciaBits.vo Patricia.vo
StringPatricia.vo: StringBits.vo
NativeRefinement.vo: PatriciaBits.vo StringBits.vo
NativeStringWorker.vo: NativeRefinement.vo StringBits.vo
StringPatriciaProof.vo: StringBits.vo StringPatricia.vo
PatriciaUnion.vo: PatriciaBits.vo Patricia.vo
PatriciaUnionProof.vo: PatriciaProof.vo PatriciaUnion.vo
StringPatriciaUnion.vo: StringBits.vo StringPatricia.vo
StringPatriciaUnionProof.vo: StringPatriciaProof.vo StringPatriciaUnion.vo
NativeHeapRefinement.vo: PatriciaUnionProof.vo StringPatriciaUnionProof.vo
HashTableBits.vo: HashTableSpec.vo
HashTableBucket.vo: HashTableSpec.vo
HashTable.vo: HashTableSpec.vo HashTableBits.vo HashTableBucket.vo
HashTableProof.vo: HashTable.vo HashTableBucket.vo
HashTableNative.vo: HashTable.vo HashTableBits.vo
HashTableSkeleton.vo: HashTableSpec.vo HashTableBits.vo

%.vo: %.v
	$(ROCQ) compile $(ROCQFLAGS) $<

clean:
	rm -f *.vo *.vos *.vok *.glob *.aux .*.aux *.lia.cache
	rm -f extracted/*.ml extracted/*.mli extracted/*.cmi extracted/*.cmo extracted/*.cmx extracted/*.o
	rm -f $(REFERENCE_DIR)/*.ml $(REFERENCE_DIR)/*.mli $(REFERENCE_DIR)/*.cmi \
	  $(REFERENCE_DIR)/*.cmo $(REFERENCE_DIR)/*.cmx $(REFERENCE_DIR)/*.o
	rm -f hashtable_reference_extracted/*.ml hashtable_reference_extracted/*.mli \
	  hashtable_reference_extracted/*.cmi hashtable_reference_extracted/*.cmo \
	  hashtable_reference_extracted/*.cmx hashtable_reference_extracted/*.o
	rm -f hashtable_skeleton_extracted/*.ml hashtable_skeleton_extracted/*.mli \
	  hashtable_skeleton_extracted/*.cmi hashtable_skeleton_extracted/*.cmo \
	  hashtable_skeleton_extracted/*.cmx hashtable_skeleton_extracted/*.o
	rm -f PatriciaMap.cmi PatriciaMap.cmo PatriciaMap.cmx PatriciaMap.o
	rm -f StringPatriciaMap.cmi StringPatriciaMap.cmo StringPatriciaMap.cmx StringPatriciaMap.o
	rm -f HashMap.cmi HashMap.cmo HashMap.cmx HashMap.o
	rm -f HashTablePrimitives.cmi HashTablePrimitives.cmo HashTablePrimitives.cmx HashTablePrimitives.o
	rm -f HashTablePrimitivesTest.cmi HashTablePrimitivesTest.cmo HashTablePrimitivesTest.cmx HashTablePrimitivesTest.o
	rm -f hashtable-reference-test hashtable-wrapper-test hashtable-wrapper-native-test hashtable-native-primitives-test
	rm -f PatriciaReference.cmi PatriciaReference.cmo PatriciaReference.cmx PatriciaReference.o
	rm -f PatriciaTest.cmi PatriciaTest.cmo PatriciaDifferentialTest.cmi \
	  PatriciaDifferentialTest.cmo PatriciaUnionTest.cmi PatriciaUnionTest.cmo \
	  PatriciaBenchmark.cmi PatriciaBenchmark.cmx PatriciaBenchmark.o \
	  PatriciaUnionProfile.cmi PatriciaUnionProfile.cmx PatriciaUnionProfile.o \
	  PatriciaReferenceProfile.cmi PatriciaReferenceProfile.cmx PatriciaReferenceProfile.o \
	  StringPrimitiveProfile.cmi StringPrimitiveProfile.cmx StringPrimitiveProfile.o \
	  PatriciaMapFilterProfile.cmi PatriciaMapFilterProfile.cmx PatriciaMapFilterProfile.o \
	  PatriciaRemoveProfile.cmi PatriciaRemoveProfile.cmx PatriciaRemoveProfile.o
	rm -f patricia-test patricia-union-test patricia-differential-test \
	  patricia-union-native-test \
	  patricia-benchmark patricia-union-profile patricia-set-profile patricia-map-filter-profile patricia-remove-profile \
	  patricia-reference-profile patricia-string-primitive-profile
