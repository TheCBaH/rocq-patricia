#!/bin/sh
# Version-pinned source audit for the OCaml primitive used by the specialized
# union realizers. This is implementation evidence only: it does not prove
# that the installed compiler binary, its generated code, or the GC satisfy
# the heap contract in NativeHeapRefinement.v.
set -eu

source_root=${1:?usage: check-ocaml-physical-equality.sh OCAML_SOURCE_ROOT}

stdlib="$source_root/stdlib/stdlib.ml"
translation="$source_root/lambda/translprim.ml"
cmmgen="$source_root/asmcomp/cmmgen.ml"
native="$source_root/asmcomp/cmm_helpers.ml"

for file in "$stdlib" "$translation" "$cmmgen" "$native"; do
  if [ ! -f "$file" ]; then
    echo "missing OCaml compiler source: $file" >&2
    exit 1
  fi
done

if ! rg -F 'external ( == ) : '\''a -> '\''a -> bool = "%eq"' "$stdlib" >/dev/null; then
  echo "OCaml source audit: Stdlib.(==) is not the %eq primitive" >&2
  exit 1
fi

if ! rg -F '"%eq", Primitive ((Pintcomp Ceq), 2);' "$translation" >/dev/null; then
  echo "OCaml source audit: %eq is not translated to Pintcomp Ceq" >&2
  exit 1
fi

if ! rg -F '| Pintcomp cmp ->' "$cmmgen" >/dev/null \
   || ! rg -F 'int_comp_caml cmp (transl env arg1) (transl env arg2) dbg' \
        "$cmmgen" >/dev/null; then
  echo "OCaml source audit: Pintcomp is not dispatched to int_comp_caml" >&2
  exit 1
fi

if ! rg -F 'let int_comp_caml cmp arg1 arg2 dbg =' "$native" >/dev/null \
   || ! rg -F 'Cop(Ccmpi cmp,' "$native" >/dev/null; then
  echo "OCaml source audit: native integer comparison lowering changed" >&2
  exit 1
fi

echo "OCaml physical-equality source audit: %eq lowers to native word comparison"
