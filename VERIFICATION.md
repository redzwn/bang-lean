# Verification record

- Lean 4.36.0-rc2 (commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`)
- Mathlib `7bcc5e95ffc0d80d94adc6f17715f224d59d209b`
- Checkers: `leanchecker`, `leanexport` and `nanoda_bin` as shipped with that toolchain
- Date: 15 November 2026

## What each check establishes

1. **Build.** `lake build` elaborates every file; Lean’s kernel checks every proof term. The script fails on any warning.
2. **Source scan.** No `sorry`, `axiom`, `native_decide`, `implemented_by` or `unsafe` in the sources.
3. **Axiom audit** ([`scripts/Audit.lean`](scripts/Audit.lean)). Every declaration defined in a `Bang.*` module, including compiler-generated auxiliaries, depends only on `propext`, `Classical.choice`, `Quot.sound`. The audit fails if it finds no declarations.
4. **Statement fingerprints** ([`scripts/Statements.lean`](scripts/Statements.lean)). The 19 main statements, as printed by `#check`, match [`scripts/statements.expected`](scripts/statements.expected). A weakened or altered statement fails this step.
5. **leanchecker.** Each module is replayed through the kernel from its stored proof terms.
6. **nanoda.** The main theorems and everything they depend on are exported with `leanexport` and type-checked by nanoda, a separate implementation in Rust, with only the three standard axioms permitted. The script fails if the export is empty or no declarations were checked.
7. **Tamper tests.** The same nanoda configuration must reject a proof using `sorry`, a proof using a new axiom, and a proof using `native_decide`; the fingerprint check must reject a swapped statement.

nanoda’s line “1 pretty printer errors: Unable to print axioms” concerns printing the axioms at the end of a run. It is not a type-checking error; the count of those is zero.

## What is not established

The three axioms, the correctness of Lean’s kernel and of nanoda, and the faithfulness of the formal statements to their informal readings are trusted. `leanchecker --fresh` (re-checking all of Mathlib) was not run. No human referee has reviewed the development.

## Transcript of `scripts/verify.sh`

```
== 1. Versions
Lean (version 4.36.0-rc2, x86_64-unknown-linux-gnu, commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a, Release)
mathlib 7bcc5e95ffc0d80d94adc6f17715f224d59d209b

== 2. Build (the Lean kernel checks every proof); warnings count as failures
Build completed successfully (18248 jobs).

== 3. No sorry, no axiom, no native_decide in the sources
none

== 4. Axiom audit of every declaration in the project
audit: 53 declarations (46 theorems) in the Bang modules; every one depends only on axioms among [propext, Classical.choice, Quot.sound]
'Bang.dist_eq_of_volume_faceOpposite_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bang.volume_faceOpposite_eq_of_dist_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bang.volume_faceOpposite_eq_iff_dist_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bang.sum_infDist_facetSpan_const_iff_dist_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bang.sum_infDist_facetSpan_eq_height' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bang.Examples.volume_faceOpposite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bang.Examples.dist_eq_of_bang' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bang.Examples.sum_infDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound]

== 5. Statements are the ones on record (scripts/statements.expected)
identical (19 statements)

== 6. leanchecker: replay every module of the project in a fresh kernel
ok  Bang.Basic
ok  Bang.Distances
ok  Bang.Corollary
ok  Bang.Examples

== 7. nanoda: an independent type checker (written in Rust) re-checks the main theorems
      and everything they depend on, down to the axioms
Checked 49107 declarations with no typechecker errors, 1 pretty printer errors: [
    "Unable to print axioms",
]

== 8. Tamper tests: each planted defect must be rejected
rejected  Sorry: unpermitted axiom "sorryAx"
rejected  Axiom: unpermitted axiom "convenient"
rejected  NativeDecide: unpermitted axiom "bad._native.native_decide.ax_1_1"
rejected  Statement: a swapped statement no longer matches scripts/statements.expected

== 9. SHA-256 of the sources
0bd82f9bc56a0009a64580e3b1eae224b644de6f8cbd485685c92379e7271b19  Bang.lean
afa7dc57100301b4e29fd9e71dd78fe02e0eb21ac0e60930448eac607d405c07  Bang/Basic.lean
6c514faafcdd333f8bb747fc323772cb7eac6b9b2d1e850fa69779b694369851  Bang/Corollary.lean
5f740a57d17c6512e8ac5b2d09d3174f08a6dc991acfd8c1f1aafa499bc0676f  Bang/Distances.lean
6c4116dfb91e8c85f60fbe2bab0e82225c7daadad821aad1aff086bd9a720fc4  Bang/Examples.lean
aec098435f4cb00e8a93bfbf32d8e528fab863316f09b6c6b56c74dc3434bfca  lakefile.toml
c18a7a46b1af0c76f2cc5d094d6f8fd9cd6486869c9a1b1f68663d8cace62eb2  lake-manifest.json
11c697aebe5b539d74f5069e497a588e7dfab1c4eeb74313f28357e351c55ca3  lean-toolchain

ALL CHECKS PASSED
```
