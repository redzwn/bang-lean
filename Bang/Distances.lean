/-
Copyright (c) 2026 redzwn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: redzwn, Claude (Anthropic)
-/
module

public import Mathlib

/-!
# Distances from a point to the facets of a simplex

The lemmas in this file are copied, with their proofs, from `Viviani/Simplex.lean` of
[redzwn/viviani-lean](https://github.com/redzwn/viviani-lean) (commit `10be5e4`, Apache 2.0, same
authors), where they are part of a formalization of Viviani's theorem. They are repeated here,
in the namespace `Bang`, so that this project builds on Mathlib alone. Nothing in
`Bang/Basic.lean` uses them; they serve only the corollary in `Bang/Corollary.lean`.

The one idea: the distance from a point to a facet of a simplex is an affine function of the
point which vanishes on that facet. Hence, if `p` has barycentric coordinates `w`,

  `dist(p, facet opposite i) = |w i| * (height of s from vertex i)`

(the signed form is Mathlib's `Affine.Simplex.signedInfDist_affineCombination`), and on the closed
simplex the distances to the facets add up to the weighted average `∑ i, w i * s.height i` of
the heights.

## Main results

* `sum_infDist_facetSpan_const_iff`: the distance sum is the same at every point of the closed
  simplex if and only if all heights are equal,
* `sum_infDist_facetSpan_const_iff_volume`: if and only if all facets have the same volume
  (by Mathlib's `Affine.Simplex.volume_eq`, base times height).

The distance to a facet always means `Metric.infDist p (facetSpan s i)`: the least distance from
`p` to the affine subspace spanned by the facet (a plane, for a tetrahedron).
-/

public section

open EuclideanGeometry Metric Affine Finset

namespace Bang

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {n : ℕ} [NeZero n]

/-- The affine span of the facet of `s` opposite vertex `i`: for a triangle, the line through the
side opposite `i`; for a tetrahedron, the plane through the face opposite `i`. -/
abbrev facetSpan (s : Simplex ℝ P n) (i : Fin (n + 1)) : AffineSubspace ℝ P :=
  affineSpan ℝ (s.points '' {i}ᶜ)

/-- The height of a simplex from vertex `i` is the distance from that vertex to the affine
span of the opposite facet. -/
theorem height_eq_infDist (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.height i = infDist (s.points i) (facetSpan s i) := by
  rw [← dist_orthogonalProjection_eq_infDist, Simplex.height, Simplex.altitudeFoot,
    Simplex.orthogonalProjectionSpan]
  simp_rw [Simplex.range_faceOpposite_points]

/-- For a point of the affine span of the simplex, the absolute value of Mathlib's signed
distance to a facet is the ordinary distance to the affine span of that facet. -/
theorem abs_signedInfDist_eq_infDist (s : Simplex ℝ P n) (i : Fin (n + 1)) {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    |s.signedInfDist i p| = infDist p (facetSpan s i) := by
  rw [← dist_orthogonalProjection_eq_infDist]
  refine AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert ?_
  rwa [affineSpan_insert_affineSpan, Set.insert_image_compl_eq_range]

/-- The signed distance to the facet opposite `i` is the barycentric weight of `i` times the
height from `i`. (A restatement of `Affine.Simplex.signedInfDist_affineCombination` in terms of
`Affine.Simplex.height`.) -/
theorem signedInfDist_affineCombination (s : Simplex ℝ P n) (i : Fin (n + 1))
    {w : Fin (n + 1) → ℝ} (hw : ∑ j, w j = 1) :
    s.signedInfDist i (univ.affineCombination ℝ s.points w) = w i * s.height i := by
  rw [s.signedInfDist_affineCombination i hw, Simplex.height, Simplex.altitudeFoot,
    dist_eq_norm_vsub]

/-- **Key lemma.** The distance from a point to the facet opposite vertex `i` is the absolute
value of its barycentric weight at `i`, times the height from `i`. -/
theorem infDist_facetSpan_affineCombination (s : Simplex ℝ P n) (i : Fin (n + 1))
    {w : Fin (n + 1) → ℝ} (hw : ∑ j, w j = 1) :
    infDist (univ.affineCombination ℝ s.points w) (facetSpan s i) = |w i| * s.height i := by
  rw [← abs_signedInfDist_eq_infDist s i (affineCombination_mem_affineSpan hw _),
    signedInfDist_affineCombination s i hw, abs_mul, abs_of_pos (s.height_pos i)]

/-- **Viviani for every simplex.** For a point of the closed simplex, with barycentric weights
`w`, the distances to the facets add up to the weighted average `∑ i, w i * s.height i` of the
heights. -/
theorem sum_infDist_facetSpan_affineCombination (s : Simplex ℝ P n)
    {w : Fin (n + 1) → ℝ} (hw : ∑ j, w j = 1) (h0 : ∀ j, 0 ≤ w j) :
    ∑ i, infDist (univ.affineCombination ℝ s.points w) (facetSpan s i) =
      ∑ i, w i * s.height i := by
  refine sum_congr rfl fun i _ ↦ ?_
  rw [infDist_facetSpan_affineCombination s i hw, abs_of_nonneg (h0 i)]

omit [NeZero n] in
/-- A point of the closed simplex is an affine combination of the vertices with nonnegative
weights. -/
theorem exists_weights_of_mem_closedInterior {s : Simplex ℝ P n} {p : P}
    (hp : p ∈ s.closedInterior) :
    ∃ w : Fin (n + 1) → ℝ, ∑ j, w j = 1 ∧ (∀ j, 0 ≤ w j) ∧
      p = univ.affineCombination ℝ s.points w := by
  obtain ⟨w, hw, hw01, rfl⟩ := hp
  exact ⟨w, hw, fun j ↦ (hw01 j).1, rfl⟩


/-! ### The distance sum on the closed simplex -/

/-- At a vertex, the distance sum is the height from that vertex. -/
theorem sum_infDist_facetSpan_point (s : Simplex ℝ P n) (j : Fin (n + 1)) :
    ∑ i, infDist (s.points j) (facetSpan s i) = s.height j := by
  have h := sum_infDist_facetSpan_affineCombination s (w := Pi.single j 1)
    (Fintype.sum_pi_single' _ _) (fun k ↦ by by_cases hk : k = j <;> simp [hk])
  rw [univ.affineCombination_piSingle ℝ s.points (mem_univ j)] at h
  simpa [Pi.single_apply] using h

/-- On the closed simplex the distance sum is at least the smallest height. -/
theorem le_sum_infDist_facetSpan {s : Simplex ℝ P n} {p : P} (hp : p ∈ s.closedInterior)
    {m : ℝ} (hm : ∀ i, m ≤ s.height i) : m ≤ ∑ i, infDist p (facetSpan s i) := by
  obtain ⟨w, hw, h0, rfl⟩ := exists_weights_of_mem_closedInterior hp
  rw [sum_infDist_facetSpan_affineCombination s hw h0]
  calc m = ∑ i, w i * m := by rw [← sum_mul, hw, one_mul]
    _ ≤ ∑ i, w i * s.height i := sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hm i) (h0 i)

/-- On the closed simplex the distance sum is at most the largest height. -/
theorem sum_infDist_facetSpan_le {s : Simplex ℝ P n} {p : P} (hp : p ∈ s.closedInterior)
    {M : ℝ} (hM : ∀ i, s.height i ≤ M) : ∑ i, infDist p (facetSpan s i) ≤ M := by
  obtain ⟨w, hw, h0, rfl⟩ := exists_weights_of_mem_closedInterior hp
  rw [sum_infDist_facetSpan_affineCombination s hw h0]
  calc ∑ i, w i * s.height i ≤ ∑ i, w i * M :=
        sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hM i) (h0 i)
    _ = M := by rw [← sum_mul, hw, one_mul]

/-- If all heights of a simplex equal `h`, the distances from any point of the closed simplex to
the facets add up to `h`. -/
theorem sum_infDist_facetSpan_eq_of_height_eq {s : Simplex ℝ P n} {h : ℝ}
    (hh : ∀ i, s.height i = h) {p : P} (hp : p ∈ s.closedInterior) :
    ∑ i, infDist p (facetSpan s i) = h :=
  le_antisymm (sum_infDist_facetSpan_le hp fun i ↦ (hh i).le)
    (le_sum_infDist_facetSpan hp fun i ↦ (hh i).ge)

/-- **Viviani and its converse, in every dimension.** The distance sum is constant on the closed
simplex if and only if all heights of the simplex are equal. -/
theorem sum_infDist_facetSpan_const_iff (s : Simplex ℝ P n) :
    (∃ c : ℝ, ∀ p ∈ s.closedInterior, ∑ i, infDist p (facetSpan s i) = c) ↔
      ∀ i j, s.height i = s.height j := by
  constructor
  · rintro ⟨c, hc⟩ i j
    rw [← sum_infDist_facetSpan_point s i, ← sum_infDist_facetSpan_point s j,
      hc _ (s.point_mem_closedInterior i), hc _ (s.point_mem_closedInterior j)]
  · intro h
    exact ⟨s.height 0, fun p hp ↦ sum_infDist_facetSpan_eq_of_height_eq (fun i ↦ h i 0) hp⟩

/-! ### Heights and facet volumes -/

/-- Height times the volume of the opposite facet is `n` times the volume of the simplex. -/
theorem height_mul_volume_faceOpposite (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.height i * (s.faceOpposite i).volume = n * s.volume := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  rw [s.volume_eq i]
  field_simp

/-- Two heights of a simplex are equal exactly when the opposite facets have equal volume. -/
theorem height_eq_iff_volume_faceOpposite_eq (s : Simplex ℝ P n) (i j : Fin (n + 1)) :
    s.height i = s.height j ↔ (s.faceOpposite i).volume = (s.faceOpposite j).volume := by
  have h := (height_mul_volume_faceOpposite s i).trans (height_mul_volume_faceOpposite s j).symm
  have hi := s.height_pos i
  have hj := s.height_pos j
  have vi := (s.faceOpposite i).volume_pos
  have vj := (s.faceOpposite j).volume_pos
  constructor
  · intro e
    rw [e] at h
    exact mul_left_cancel₀ hj.ne' h
  · intro e
    rw [e] at h
    exact mul_right_cancel₀ vj.ne' h

/-- The distance sum is constant on the closed simplex if and only if all facets have the same
volume. -/
theorem sum_infDist_facetSpan_const_iff_volume (s : Simplex ℝ P n) :
    (∃ c : ℝ, ∀ p ∈ s.closedInterior, ∑ i, infDist p (facetSpan s i) = c) ↔
      ∀ i j, (s.faceOpposite i).volume = (s.faceOpposite j).volume := by
  simp_rw [sum_infDist_facetSpan_const_iff, height_eq_iff_volume_faceOpposite_eq]

end Bang
