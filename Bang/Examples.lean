/-
Copyright (c) 2026 redzwn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: redzwn, Claude (Anthropic)
-/
module

public import Bang.Corollary

/-!
# Sanity checks on a concrete tetrahedron

The hypotheses of the theorems are satisfied by a genuine tetrahedron that is not regular, and
the theorems say what they should on it. In `EuclideanSpace ℝ (Fin 3)` take four alternate
corners of the box `1 × 2 × 3`:

  `A₀ = (0, 0, 0)`, `B₀ = (1, 2, 0)`, `C₀ = (1, 0, 3)`, `D₀ = (0, 2, 3)`.

Its six edges are face diagonals of the box, so opposite edges are equal in pairs, with the three
different lengths `√5`, `√10`, `√13`. Each face is a triangle with these three sides, of area
`7 / 2`.
-/

public section

open Metric Affine Finset

namespace Bang.Examples

/-- The point `(0, 0, 0)`. -/
noncomputable def A₀ : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 0]

/-- The point `(1, 2, 0)`. -/
noncomputable def B₀ : EuclideanSpace ℝ (Fin 3) := !₂[1, 2, 0]

/-- The point `(1, 0, 3)`. -/
noncomputable def C₀ : EuclideanSpace ℝ (Fin 3) := !₂[1, 0, 3]

/-- The point `(0, 2, 3)`. -/
noncomputable def D₀ : EuclideanSpace ℝ (Fin 3) := !₂[0, 2, 3]

/-- The four points are affinely independent: they span a genuine tetrahedron. -/
theorem affineIndependent : AffineIndependent ℝ ![A₀, B₀, C₀, D₀] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw h i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) h
  simp [Fin.sum_univ_four, A₀, B₀, C₀, D₀] at h0 h1 h2 hw
  fin_cases i <;> simp <;> linarith

/-- The tetrahedron with vertices `A₀`, `B₀`, `C₀`, `D₀`. -/
noncomputable def disphenoid : Simplex ℝ (EuclideanSpace ℝ (Fin 3)) 3 :=
  ⟨![A₀, B₀, C₀, D₀], affineIndependent⟩

/-- The edge `A₀B₀` has length `√5`. -/
theorem dist_A₀_B₀ : dist A₀ B₀ = Real.sqrt 5 := by
  rw [EuclideanSpace.dist_eq]
  simp [A₀, B₀, Fin.sum_univ_three, Real.dist_eq, sq_abs]
  norm_num

/-- The edge `C₀D₀` has length `√5`. -/
theorem dist_C₀_D₀ : dist C₀ D₀ = Real.sqrt 5 := by
  rw [EuclideanSpace.dist_eq]
  simp [C₀, D₀, Fin.sum_univ_three, Real.dist_eq, sq_abs]
  norm_num

/-- The edge `A₀C₀` has length `√10`. -/
theorem dist_A₀_C₀ : dist A₀ C₀ = Real.sqrt 10 := by
  rw [EuclideanSpace.dist_eq]
  simp [A₀, C₀, Fin.sum_univ_three, Real.dist_eq, sq_abs]
  norm_num

/-- The edge `B₀D₀` has length `√10`. -/
theorem dist_B₀_D₀ : dist B₀ D₀ = Real.sqrt 10 := by
  rw [EuclideanSpace.dist_eq]
  simp [B₀, D₀, Fin.sum_univ_three, Real.dist_eq, sq_abs]
  norm_num

/-- The edge `A₀D₀` has length `√13`. -/
theorem dist_A₀_D₀ : dist A₀ D₀ = Real.sqrt 13 := by
  rw [EuclideanSpace.dist_eq]
  simp [A₀, D₀, Fin.sum_univ_three, Real.dist_eq, sq_abs]
  norm_num

/-- The edge `B₀C₀` has length `√13`. -/
theorem dist_B₀_C₀ : dist B₀ C₀ = Real.sqrt 13 := by
  rw [EuclideanSpace.dist_eq]
  simp [B₀, C₀, Fin.sum_univ_three, Real.dist_eq, sq_abs]
  norm_num

/-- Opposite edges of the example are equal in pairs. -/
theorem dist_eq :
    dist (disphenoid.points 0) (disphenoid.points 1) =
        dist (disphenoid.points 2) (disphenoid.points 3) ∧
      dist (disphenoid.points 0) (disphenoid.points 2) =
        dist (disphenoid.points 1) (disphenoid.points 3) ∧
      dist (disphenoid.points 0) (disphenoid.points 3) =
        dist (disphenoid.points 1) (disphenoid.points 2) :=
  ⟨dist_A₀_B₀.trans dist_C₀_D₀.symm, dist_A₀_C₀.trans dist_B₀_D₀.symm,
    dist_A₀_D₀.trans dist_B₀_C₀.symm⟩

/-- The example is not a regular tetrahedron: two edges at the same vertex have different
lengths. -/
theorem dist_ne :
    dist (disphenoid.points 0) (disphenoid.points 1) ≠
      dist (disphenoid.points 0) (disphenoid.points 2) := by
  change dist A₀ B₀ ≠ dist A₀ C₀
  rw [dist_A₀_B₀, dist_A₀_C₀]
  intro h
  have := Real.sqrt_inj (by norm_num : (0 : ℝ) ≤ 5) (by norm_num : (0 : ℝ) ≤ 10) |>.1 h
  norm_num at this

/-- **The hypothesis of Bang's theorem is satisfiable.** The four faces of the example have equal
area, although the tetrahedron is not regular. -/
theorem volume_faceOpposite_eq (i j : Fin 4) :
    (disphenoid.faceOpposite i).volume = (disphenoid.faceOpposite j).volume :=
  volume_faceOpposite_eq_of_dist_eq disphenoid dist_eq.1 dist_eq.2.1 dist_eq.2.2 i j

/-- Each face of the example has area `7 / 2`. -/
theorem volume_faceOpposite (i : Fin 4) : (disphenoid.faceOpposite i).volume = 7 / 2 := by
  rw [volume_faceOpposite_eq i 3]
  have h := (four_mul_volume_faceOpposite_sq disphenoid).2.2.2
  have d₁ := dist_sq_eq' (disphenoid.points 0) (disphenoid.points 1)
  have d₂ := dist_sq_eq' (disphenoid.points 0) (disphenoid.points 2)
  have d₃ := dist_sq_eq (disphenoid.points 1) (disphenoid.points 2) (disphenoid.points 0)
  have e₁ : dist (disphenoid.points 0) (disphenoid.points 1) ^ 2 = 5 := by
    change dist A₀ B₀ ^ 2 = 5
    rw [dist_A₀_B₀, Real.sq_sqrt (by norm_num)]
  have e₂ : dist (disphenoid.points 0) (disphenoid.points 2) ^ 2 = 10 := by
    change dist A₀ C₀ ^ 2 = 10
    rw [dist_A₀_C₀, Real.sq_sqrt (by norm_num)]
  have e₃ : dist (disphenoid.points 1) (disphenoid.points 2) ^ 2 = 13 := by
    change dist B₀ C₀ ^ 2 = 13
    rw [dist_B₀_C₀, Real.sq_sqrt (by norm_num)]
  have hv : (disphenoid.faceOpposite 3).volume ^ 2 = (7 / 2) ^ 2 := by nlinarith
  exact (pow_left_inj₀ (disphenoid.faceOpposite 3).volume_pos.le (by norm_num) two_ne_zero).1 hv

/-- Bang's theorem applied to the example returns the equal opposite edges: the theorem is not
vacuous. -/
theorem dist_eq_of_bang :
    dist A₀ B₀ = dist C₀ D₀ ∧ dist A₀ C₀ = dist B₀ D₀ ∧ dist A₀ D₀ = dist B₀ C₀ :=
  dist_eq_of_volume_faceOpposite_eq disphenoid volume_faceOpposite_eq

/-- On the example the distances from a point of the closed tetrahedron to the four face planes
add up to the same number wherever the point is. -/
theorem sum_infDist_eq {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ disphenoid.closedInterior) :
    ∑ i, infDist p (facetSpan disphenoid i) = disphenoid.height 0 :=
  sum_infDist_facetSpan_eq_height disphenoid dist_eq.1 dist_eq.2.1 dist_eq.2.2 hp

end Bang.Examples
