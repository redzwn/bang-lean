# Claims and evidence

Every claim we make in public about this project, with what supports it and how to check it. If a sentence about the project is not covered here, we should not be saying it.

| Claim | Evidence | Reproduce |
| --- | --- | --- |
| If the four faces of a tetrahedron have equal area, opposite edges are equal in pairs | `Bang.dist_eq_of_volume_faceOpposite_eq` | `lake build` |
| The converse, and the equivalence | `Bang.volume_faceOpposite_eq_of_dist_eq`, `Bang.volume_faceOpposite_eq_iff_dist_eq` | `lake build` |
| The statements hold in any Euclidean affine space; the ambient dimension is not assumed to be 3 | the hypotheses of those theorems | read the statements |
| In a tetrahedron the distance sum to the four face planes is constant on the closed tetrahedron ⇔ opposite edges are equal in pairs; the constant is then the height | `Bang.sum_infDist_facetSpan_const_iff_dist_eq`, `Bang.sum_infDist_facetSpan_eq_height` | `lake build` |
| The hypotheses are satisfiable by a non-regular tetrahedron: corners (0,0,0), (1,2,0), (1,0,3), (0,2,3), edges √5, √10, √13, every face of area 7/2 | `Bang.Examples.affineIndependent`, `dist_eq`, `dist_ne`, `volume_faceOpposite`, `dist_eq_of_bang` | `lake build` |
| The main theorem depends on Mathlib only | `Bang/Basic.lean` imports `Mathlib` and nothing else | read the imports |
| No `sorry`; only `propext`, `Classical.choice`, `Quot.sound`, for all 53 declarations | `scripts/Audit.lean` | `lake env lean scripts/Audit.lean` |
| Builds without warnings on Lean 4.36.0-rc2, Mathlib `7bcc5e95` | step 2 of the transcript | `scripts/verify.sh` |
| Re-checked by `leanchecker` (4 modules) and by nanoda (49,107 declarations) | steps 6–7 of the transcript | `scripts/verify.sh` |
| Four planted defects are rejected | step 8 of the transcript | `scripts/verify.sh` |
| We are not aware of an earlier formalization of this theorem in any proof assistant; the proof was written independently | the search recorded in [SEARCH.md](SEARCH.md); working record of the project | repeat the searches |
| The proof route (the area-vector argument carried out on the Gram matrix) was found by Claude Fable 5.2 working with redzwn | working record of the project | not machine-checkable; stated as our account |

## Things we do not claim

- That this is the first, or the only, formalization of this theorem in Lean or in any proof assistant. Our search is recorded in [SEARCH.md](SEARCH.md); a search can miss things.
- That any of the mathematics is new. The theorem is classical (see the README for sources). Carrying out the area-vector argument with Gram cofactors is elementary linear algebra, and we have not searched the literature for that exact presentation.
- That Bang’s 1897 theorem on the inscribed sphere is formalized here. It is not; only its equal-area consequence is.
- That the stronger pairwise statement (Klain, arXiv:2112.14918) is formalized here. It is not.
- That the four faces are proved *congruent* as a formal statement about isometries. What is proved is that opposite edges are equal in pairs, from which the faces have the same three side lengths.
- That the lemmas in `Bang/Distances.lean` are new to this project: they are copied from redzwn/viviani-lean, and rest on Mathlib’s `Affine.Simplex.signedInfDist_affineCombination` and `Affine.Simplex.volume_eq`.
- That anything was reviewed by a person other than the authors, or that “nothing is taken on trust”.
- Any ranking against other projects.
