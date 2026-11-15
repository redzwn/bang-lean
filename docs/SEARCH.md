# Search for earlier formalizations

Run on 15 November 2026. The question: has the statement “a tetrahedron whose four faces have equal area has opposite edges equal in pairs” (or its consequence for distance sums) been formalized before, in Lean or another proof assistant?

**Result: no earlier formalization was found.** This is a record of where we looked, not a proof that none exists. Queries and results are given so that the search can be repeated.

| Where | Query | Result |
| --- | --- | --- |
| Mathlib at `7bcc5e95` (`Mathlib/`, `Archive/`, `Counterexamples/`, `docs/`), local text search | `disphenoid`, `equifacial`, `equiareal`, `isosceles tetrahedr`, `Bang's theorem`, `Bang theorem` (case-insensitive) | One file matches: `docs/1000.yaml`, see next row. No Lean file matches. |
| The 1000+ theorems list as shipped in Mathlib ([`docs/1000.yaml`](https://github.com/leanprover-community/mathlib4/blob/master/docs/1000.yaml); rendered at [leanprover-community.github.io/1000.html](https://leanprover-community.github.io/1000.html)) | `Bang`, `Q30591105` | One entry, `Q7686760: Bang's theorem`, with no formalization recorded. `Q30591105` (“Bang's theorem on tetrahedra”) is not in the list. |
| GitHub code search (all public code), Lean | `disphenoid language:Lean`; `equifacial language:Lean`; `equiareal language:Lean`; `"isosceles tetrahedron" language:Lean`; `"Bang's theorem" language:Lean`; `"disphenoid" theorem language:Lean`; `"equal area" tetrahedron "opposite edges" language:Lean` | 0 results each. Control queries on the same day: `tetrahedron language:Lean` 860 results, `signedInfDist language:Lean` 24. |
| GitHub repository search | `disphenoid language:Lean`; `equifacial tetrahedron language:Lean`; `"isosceles tetrahedron" language:Lean`; `"Bang's theorem" language:Lean`; `"Bang's theorem" tetrahedron` | 0 results each, apart from this repository. |
| Isabelle and the Archive of Formal Proofs (GitHub code search, including the mirror `isabelle-prover/mirror-afp-devel`) | `disphenoid language:Isabelle`; `equifacial language:Isabelle`; `"Bang" tetrahedron language:Isabelle`; `Bang tetrahedron repo:isabelle-prover/mirror-afp-devel`; `equal area tetrahedron repo:isabelle-prover/mirror-afp-devel` | 0 results each. Control: `tetrahedron language:Isabelle` 13 results. |
| Rocq (Coq) and GeoCoq (GitHub code search) | `disphenoid language:Coq`; `equifacial language:Coq`; `"isosceles tetrahedron" language:Coq`; `tetrahedron repo:GeoCoq/GeoCoq` | 0 results each. |
| HOL Light (GitHub code search in `jrh13/hol-light`) | `disphenoid`; `tetrahedron` | `disphenoid`: 0. `tetrahedron`: 2 files (`100/platonic.ml`, `Multivariate/flyspeck.ml`), neither on this theorem by their names; their contents were not read. |
| Metamath (GitHub code search) | `tetrahedron repo:metamath/set.mm`; `disphenoid extension:mm` | 0 results each. |
| Mizar | `disphenoid extension:miz` on GitHub code search; web search below | 0 results. The Mizar Mathematical Library itself was not searched directly. |
| Lean Zulip | Web search: `Lean Zulip tetrahedron "equal area" faces disphenoid OR equifacial OR "Bang"` | No relevant thread found. The Zulip archive was not searched with its own search. |
| arXiv ([export API](https://export.arxiv.org/api/query)) | `all:"Bang's theorem" AND all:tetrahedron`; `all:"Bang's theorem" AND all:formalization`; `all:disphenoid AND all:formalization`; `all:tetrahedron AND all:"equal area" AND all:Lean`; `all:equifacial AND all:"proof assistant"` | 0 results each. |
| Zenodo ([records API](https://zenodo.org/api/records)) | `"Bang's theorem" tetrahedron`; `equifacial tetrahedron Lean`; `disphenoid formalization`; `tetrahedron "equal area" faces formal proof` | Many loosely matching records (the search is fuzzy); the first six of each were read by title and none concerns this theorem or a formalization of it. |
| General web search (stands in for Google Scholar, which was not queried directly) | `Lean 4 Mathlib formalization "equifacial" OR "disphenoid" OR "isosceles tetrahedron" theorem equal face areas`; `github lean "disphenoid" tetrahedron formal proof`; `Isabelle AFP tetrahedron "equal areas" faces congruent "Bang's theorem" formalization`; `"Bang's theorem" tetrahedron Coq OR Rocq OR GeoCoq OR "HOL Light" OR Mizar OR Metamath formalized`; `zenodo formalization tetrahedron equal face areas congruent faces Lean OR Isabelle OR Coq "equifacial" OR "isosceles tetrahedron"` | Only informal mathematics (Wikipedia, MathWorld, cut-the-knot, the papers cited in the README). No formalization. |

## Limits of this search

- Google Scholar, the Lean Zulip archive’s own search, the Mizar Mathematical Library and Metamath’s own site search were not queried directly.
- Code search only finds public repositories, and only if they use one of the words we tried. A formalization stated purely in symbols, under a different name, would be missed.
- Private work, and work published after the date above, is not covered.

## Related formal work that was found

- redzwn/viviani-lean (the companion project) proves the easy direction: opposite edges equal ⇒ equal face areas ⇒ constant distance sum.
- The earlier Lean formalizations of Viviani’s theorem cited in that project’s README. Their code was not consulted for this project, and we do not know whether they treat tetrahedra with faces of equal area.
