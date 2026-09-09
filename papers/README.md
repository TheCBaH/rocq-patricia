# Patricia research papers: citations and provenance

Last updated: 2026-09-09. These PDFs support the investigation and separate
tracker in [patricia-native-verification.md](../patricia-native-verification.md).
Machine-readable citations are in [references.bib](references.bib). The PDF
contents have not been edited; publication metadata and acquisition history
are recorded here rather than inserted into the papers.

## Okasaki and Gill — Fast Mergeable Integer Maps

[Local PDF](okasaki-gill-1998-fast-mergeable-integer-maps.pdf)

Chris Okasaki and Andy Gill. **Fast Mergeable Integer Maps.** In *ACM SIGPLAN
Workshop on ML*, pp. 77–86, September 1998.
BibTeX key: `OkasakiGill1998`.

Citation source: the [University of Kansas Functional Programming Group's
publication record](https://ku-fpg.github.io/papers/Okasaki-98-IntMap/).
That record links a historical PDF at
`http://www.ittc.ku.edu/csdl/fpg/files/Okasaki-98-IntMap.pdf`; its HTTPS equivalent
returned HTTP 404 when checked on 2026-09-09.

Local-file provenance: already present in the workspace as
`Okasaki and Gill - 1998 - Fast Mergeable Integer Maps.pdf` before this
investigation. Moved here and renamed on 2026-09-09. Its original download URL,
acquisition date and version were not recorded, so the publication record is
a bibliographic authority, not a verified download origin for these bytes.
No publisher DOI has been established here.

Relevance: the integer Patricia-tree algorithms and merge performance that
motivate the project; not a verification of the current native realizers.

## Leroy — Well-founded recursion done right

[Local PDF](leroy-well-founded-recursion.pdf)

Xavier Leroy. **Well-founded recursion done right (Coq programming pearl).**
*CoqPL 2024: The Tenth International Workshop on Coq for Programming Languages*,
London, United Kingdom, January 2024. Workshop extended abstract.
BibTeX key: `Leroy2024WellFounded`.

Publication record: [CoqPL 2024 program and attachments](https://popl24.sigplan.org/details/CoqPL-2024-papers/2/Well-founded-recursion-done-right).
Download origin: [author-hosted PDF](https://xavierleroy.org/publi/wf-recursion.pdf),
retrieved 2026-09-09. The author-hosted file is retained as retrieved; its exact
revision is not inferred from the workshop date.

Relevance: structural recursion on an accessibility proof that disappears
during extraction, a candidate for removing union-worker fuel and closures.

## Allain and Scherer — Zoo

[Local PDF](allain-scherer-2026-zoo.pdf)

Clément Allain and Gabriel Scherer. **Zoo: A Framework for the Verification of
Concurrent OCaml 5 Programs using Separation Logic.** *Proceedings of the ACM
on Programming Languages* 10, POPL, Article 59, January 2026, 28 pages.
[DOI: 10.1145/3776701](https://doi.org/10.1145/3776701).
BibTeX key: `AllainScherer2026Zoo`.

Download origin: [author-hosted PDF](https://clef-men.github.io/publications/allain-scherer-26-zoo.pdf),
retrieved 2026-09-09. Publication metadata is also available from the
[POPL 2026 record](https://popl26.sigplan.org/details/POPL-2026-popl-research-papers/61/Zoo-A-Framework-for-the-Verification-of-Concurrent-OCaml-5-Programs-using-Separation).

Relevance: verification of OCaml source through a formal language model,
including the subtleties of physical equality for immutable structures.

## Forster, Sozeau and Tabareau — Verified Extraction

[Local PDF](forster-sozeau-tabareau-2024-verified-extraction.pdf)

Yannick Forster, Matthieu Sozeau and Nicolas Tabareau. **Verified Extraction
from Coq to OCaml.** *Proceedings of the ACM on Programming Languages* 8,
PLDI, 2024, pp. 52–75.
[DOI: 10.1145/3656379](https://doi.org/10.1145/3656379).
BibTeX key: `ForsterSozeauTabareau2024Extraction`.

Download origin: [HAL full text](https://inria.hal.science/hal-04329663/file/main.pdf),
retrieved 2026-09-09 via the link on
[Yannick Forster's publication list](https://yforster.de/).
Repository identifier: `hal-04329663`. The unversioned HAL URL may resolve to a
different revision later; the checksum below identifies this local copy.
Publication metadata: [Rocq publication record](https://rocq-prover.org/papers/verified-extraction-from-coq-to-ocaml).

Relevance: verified extraction to Malfunction and the remaining compilation,
foreign-interface and interoperability boundaries.

## File identity

SHA-256 digests recorded on 2026-09-09 identify the stored copies. They do not
certify the publication content or establish an unknown acquisition origin.

| PDF | SHA-256 |
| --- | --- |
| `okasaki-gill-1998-fast-mergeable-integer-maps.pdf` | `8dbd81386104b5fa9102e0a8f8e83dce67cd6ad37b50faca5bdb36950eba0d39` |
| `leroy-well-founded-recursion.pdf` | `356079f6033da9974a474701d5c60ee0836047ae9239806f093e94e97160dd90` |
| `allain-scherer-2026-zoo.pdf` | `dcef44093e827f69d8b99a9c5549f6d731b1120857adde8e081e05c21c1f8bea` |
| `forster-sozeau-tabareau-2024-verified-extraction.pdf` | `849155927058f898f65b8b53c04a4a6991ef87ae60819f0b666fcd0a98a4f60f` |

Recompute with `sha256sum papers/*.pdf` from the parent directory.
Additional publications cited in the verification plan, including CFML and
cost reasoning, currently have external links rather than local PDF copies.
