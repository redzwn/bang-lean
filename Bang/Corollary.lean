/-
Copyright (c) 2026 redzwn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: redzwn, Claude (Anthropic)
-/
module

public import Bang.Basic
public import Bang.Distances

/-!
# The corollary: Viviani's theorem and its converse for the tetrahedron

Viviani's theorem says that in an equilateral triangle the distances from a point to the three
sides add up to the height, wherever the point is; and the equilateral triangles are the only
triangles with a constant distance sum. In a tetrahedron the distance sum is constant exactly
when the four faces have equal area (`sum_infDist_facetSpan_const_iff_volume`). Bang's theorem
turns that into a statement about edges:

* `sum_infDist_facetSpan_const_iff_dist_eq`: the sum of the distances from a point of the closed
  tetrahedron to the four face planes is the same at every point if and only if opposite edges
  are equal in pairs.
* `sum_infDist_facetSpan_eq_height`: in that case the sum is the height of the tetrahedron.

So the tetrahedra with the Viviani property are the disphenoids, not only the regular ones.
-/

public section

open EuclideanGeometry Metric Affine Finset

namespace Bang

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Viviani's theorem and its converse for the tetrahedron.** The sum of the distances from a
point of the closed tetrahedron to the four face planes is the same at every point if and only
if opposite edges are equal in pairs. -/
theorem sum_infDist_facetSpan_const_iff_dist_eq (s : Simplex ℝ P 3) :
    (∃ c : ℝ, ∀ p ∈ s.closedInterior, ∑ i, infDist p (facetSpan s i) = c) ↔
      dist (s.points 0) (s.points 1) = dist (s.points 2) (s.points 3) ∧
      dist (s.points 0) (s.points 2) = dist (s.points 1) (s.points 3) ∧
      dist (s.points 0) (s.points 3) = dist (s.points 1) (s.points 2) := by
  rw [sum_infDist_facetSpan_const_iff_volume, volume_faceOpposite_eq_iff_dist_eq]

/-- **Viviani's theorem for a disphenoid.** If opposite edges of a tetrahedron are equal in
pairs, the distances from any point of the closed tetrahedron to the four face planes add up to
the height of the tetrahedron (all four heights are equal). -/
theorem sum_infDist_facetSpan_eq_height (s : Simplex ℝ P 3)
    (h₁ : dist (s.points 0) (s.points 1) = dist (s.points 2) (s.points 3))
    (h₂ : dist (s.points 0) (s.points 2) = dist (s.points 1) (s.points 3))
    (h₃ : dist (s.points 0) (s.points 3) = dist (s.points 1) (s.points 2)) {p : P}
    (hp : p ∈ s.closedInterior) :
    ∑ i, infDist p (facetSpan s i) = s.height 0 :=
  sum_infDist_facetSpan_eq_of_height_eq
    (fun i ↦ (height_eq_iff_volume_faceOpposite_eq s i 0).2
      (volume_faceOpposite_eq_of_dist_eq s h₁ h₂ h₃ i 0)) hp

end Bang
