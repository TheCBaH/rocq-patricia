# Source hash-table API inventory

This records the kernel-checked source API.  `E` is the key equivalence
relation, `eqb` reflects `E`, and equivalent keys have equal hashes at every
seed.  Every theorem below that mentions a valid map assumes those three
callback laws explicitly.

| API requirement | Theorem(s) | Additional explicit hypotheses |
| --- | --- | --- |
| Lookup and membership describe flattened bindings | `get_binding_iff`, `mem_binding_iff`, `get_of_list_binding_iff`, `mem_of_list_binding_iff` | Valid map and a bounded query hash; bulk forms also require every input hash to be bounded. |
| Update and removal preserve the pointwise map | `get_after_set`, `get_after_remove`, and their `*_other` / `*_equiv` forms | Valid map plus bounded query and, for `set`, bounded updated-key hashes. |
| Singleton observations | `get_singleton_query`, `mem_singleton_query` | The queried and stored key route to the same hash. |
| First-wins bulk observations | `get_of_list_first_binding`, `mem_of_list_first_binding` | Every input and queried hash is bounded.  The independent `first_binding` scan selects the first equivalent input pair. |
| Representative behavior | `elements_set_retains_representative`, `elements_set_absent`, `elements_add_first_present`, `elements_of_list_first_binding_iff`, `first_binding_none_no_element` | Valid accumulator/map and the relevant bounded hashes.  These prove resident retention, absent supplied-key insertion, exact selected-pair enumeration, and the no-match case. |
| Enumeration and emptiness | `elements_keys_nodup`, `is_empty_iff_get_none` | Valid map; emptiness additionally uses the callback laws. |
| Validity, uniqueness, and seeds | `table_wf_empty`, `table_wf_set`, `table_wf_remove`, `table_wf_of_list`, `wf_bindings_nodup`, `set_seed`, `remove_seed` | The operation's updated/input keys have bounded hashes. |
| Extensional maps | `table_extensional_equivalence`, `table_extensional_set`, `table_extensional_remove`, `table_extensional_mem`, `table_extensional_is_empty` | Update/remove congruence requires valid maps and query bounds at both map seeds; `set` also requires the updated key bounded at both seeds.  Empty-observer equality requires valid maps and callback laws. |

`elements_of_list_first_binding_iff` identifies every enumerated pair with the
representative/value selected by its first-match scan; `first_binding_none_no_element`
excludes any equivalent element in the no-match case. Traversal order remains
intentionally unspecified.
