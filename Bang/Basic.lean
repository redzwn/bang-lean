/-
Copyright (c) 2026 redzwn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: redzwn, Claude (Anthropic)
-/
module

public import Mathlib

/-!
# Tetrahedra with faces of equal area (Bang's theorem on equifacial tetrahedra)

If the four faces of a tetrahedron have equal area, then opposite edges are equal in pairs: the
tetrahedron is a *disphenoid* (also called isosceles or equifacial), and its four faces are
congruent triangles.

A note on the name. Strictly, *Bang's theorem on tetrahedra* (A. S. Bang, 1897) is a statement
about the inscribed sphere: joining its point of tangency on each face to the vertices of that
face gives the same three angles on every face. The statement proved here is its well-known
consequence, and is itself commonly called Bang's theorem; see B. H. Brown, *Theorem of Bang.
Isosceles tetrahedra*, Amer. Math. Monthly 33 (1926), 224-226, and M. Hajja and F. Saidi, *A note
on Bang's theorem on equifacial tetrahedra*, J. Geom. Graph. 8 (2004), 163-169. The proof below
does not use the inscribed sphere.

## The proof

Write `a`, `b`, `c` for the edge vectors from vertex `0`, and

  `x = ‖a‖²`, `y = ‖b‖²`, `z = ‖c‖²`, `p = ⟪b, c⟫`, `q = ⟪a, c⟫`, `r = ⟪a, b⟫`

for the entries of their Gram matrix `G`. The classical argument uses the four area vectors of
the faces, which add up to zero. In three dimensions the area vectors of the faces through
vertex `0` are `b × c`, `c × a`, `a × b`, and their inner products are the cofactors of `G`:

  `‖b × c‖² = y z - p²`,  `⟪b × c, c × a⟫ = p q - r z`,  and so on.

So the argument can be carried out with the six numbers `x, y, z, p, q, r` alone, without a cross
product, an orientation, or any assumption on the dimension of the ambient space:

* `four_mul_volume_sq`: four times the squared area of a triangle is `‖u‖² ‖v‖² - ⟪u, v⟫²`, for
  `u`, `v` two of its edge vectors (from Heron's formula in Mathlib).
* `four_mul_volume_faceOpposite_sq`: this, for each of the four faces of a tetrahedron.
* `eq_of_cofactor_eq`: the algebraic heart. If the four squared areas agree, then
  `(z - ‖a - b‖²) * det G = 0`. This is the identity `adj (adj G) = det G • G` in disguise.
* `gram_det_ne_zero`: `det G ≠ 0`, because the vertices are affinely independent.

## Main results

* `dist_eq_of_volume_faceOpposite_eq`: **Bang's theorem** (in the equal-area form above).
* `volume_faceOpposite_eq_of_dist_eq`: the converse. If opposite edges are equal in pairs, the
  four faces have equal area.
* `volume_faceOpposite_eq_iff_dist_eq`: the two together.

Everything is stated for `s : Affine.Simplex ℝ P 3` in an arbitrary Euclidean affine space `P`;
the face opposite vertex `i` is `s.faceOpposite i` and its area is Mathlib's
`Affine.Simplex.volume`.
-/

public section

open EuclideanGeometry Affine
open scoped RealInnerProductSpace

namespace Bang

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Heron's formula in Gram form.** Four times the squared area of a triangle is
`‖u‖² ‖v‖² - ⟪u, v⟫²`, where `u` and `v` are the edge vectors from vertex `0`. -/
theorem four_mul_volume_sq (t : Triangle ℝ P) :
    4 * t.volume ^ 2 =
      ‖t.points 1 -ᵥ t.points 0‖ ^ 2 * ‖t.points 2 -ᵥ t.points 0‖ ^ 2 -
        ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫ ^ 2 := by
  have H := t.volume_sq_eq_mul_sub_mul_sub_mul_sub (i₁ := 0) (i₂ := 1) (i₃ := 2)
    (by decide) (by decide) (by decide)
  have h : dist (t.points 1) (t.points 2) ^ 2 =
      ‖t.points 1 -ᵥ t.points 0‖ ^ 2 + ‖t.points 2 -ᵥ t.points 0‖ ^ 2 -
        2 * ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫ := by
    rw [dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right _ _ (t.points 0), norm_sub_sq_real]
    ring
  rw [dist_comm (t.points 0) (t.points 1), dist_comm (t.points 0) (t.points 2),
    dist_eq_norm_vsub V (t.points 1), dist_eq_norm_vsub V (t.points 2) (t.points 0)] at H
  have h' : ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫ =
      (‖t.points 1 -ᵥ t.points 0‖ ^ 2 + ‖t.points 2 -ᵥ t.points 0‖ ^ 2 -
        dist (t.points 1) (t.points 2) ^ 2) / 2 := by
    linarith
  rw [h']
  linear_combination 4 * H

/-- **The algebraic heart of Bang's theorem.** Let `x, y, z, p, q, r` be the entries of the Gram
matrix of three vectors `a, b, c`. If the four quantities `y z - p²`, `x z - q²`, `x y - r²` and
`‖b - a‖² ‖c - a‖² - ⟪b - a, c - a⟫²` (four times the squared areas of the faces of the
tetrahedron with edge vectors `a, b, c`) are equal, and the Gram determinant is not zero, then
`‖c‖² = ‖a - b‖²`. -/
theorem eq_of_cofactor_eq {x y z p q r : ℝ}
    (hΔ : x * y * z + 2 * p * q * r - x * p ^ 2 - y * q ^ 2 - z * r ^ 2 ≠ 0)
    (h₁ : y * z - p ^ 2 = x * z - q ^ 2) (h₂ : y * z - p ^ 2 = x * y - r ^ 2)
    (h₃ : y * z - p ^ 2 = (x + y - 2 * r) * (x + z - 2 * q) - (x + p - q - r) ^ 2) :
    z = x + y - 2 * r := by
  have h : (z - (x + y - 2 * r)) *
      (x * y * z + 2 * p * q * r - x * p ^ 2 - y * q ^ 2 - z * r ^ 2) = 0 := by
    linear_combination
      (-(y * z - p ^ 2) +
          (q * r - p * x + (r * p - q * y) + (x * y - r ^ 2) - (p * q - r * z)) / 2) * h₁ +
        ((y * z - p ^ 2) -
          (q * r - p * x + (r * p - q * y) + (x * y - r ^ 2) - (p * q - r * z)) / 2) * h₂ +
        ((x * y - r ^ 2) -
          (q * r - p * x + (r * p - q * y) + (x * y - r ^ 2) - (p * q - r * z)) / 2) * h₃
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right hΔ)

/-- The Gram determinant of the three edge vectors from vertex `0` of a tetrahedron is not
zero. -/
theorem gram_det_ne_zero (s : Simplex ℝ P 3) :
    ‖s.points 1 -ᵥ s.points 0‖ ^ 2 * ‖s.points 2 -ᵥ s.points 0‖ ^ 2 *
        ‖s.points 3 -ᵥ s.points 0‖ ^ 2 +
      2 * ⟪s.points 2 -ᵥ s.points 0, s.points 3 -ᵥ s.points 0⟫ *
        ⟪s.points 1 -ᵥ s.points 0, s.points 3 -ᵥ s.points 0⟫ *
        ⟪s.points 1 -ᵥ s.points 0, s.points 2 -ᵥ s.points 0⟫ -
      ‖s.points 1 -ᵥ s.points 0‖ ^ 2 *
        ⟪s.points 2 -ᵥ s.points 0, s.points 3 -ᵥ s.points 0⟫ ^ 2 -
      ‖s.points 2 -ᵥ s.points 0‖ ^ 2 *
        ⟪s.points 1 -ᵥ s.points 0, s.points 3 -ᵥ s.points 0⟫ ^ 2 -
      ‖s.points 3 -ᵥ s.points 0‖ ^ 2 *
        ⟪s.points 1 -ᵥ s.points 0, s.points 2 -ᵥ s.points 0⟫ ^ 2 ≠ 0 := by
  have hli : LinearIndependent ℝ (fun i : Fin 3 ↦ s.points i.succ -ᵥ s.points 0) :=
    ((affineIndependent_iff_linearIndependent_vsub ℝ _ 0).1 s.independent).comp
      (fun i : Fin 3 ↦ ⟨i.succ, Fin.succ_ne_zero i⟩)
      (fun i j hij ↦ Fin.succ_injective _ (congrArg Subtype.val hij))
  have h := Matrix.det_gram_ne_zero_iff_linearIndependent.2 hli
  rw [Matrix.det_fin_three] at h
  have h23 : Fin.succ (2 : Fin 3) = 3 := rfl
  simp only [Matrix.gram_apply, real_inner_self_eq_norm_sq, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, h23] at h
  rw [real_inner_comm (s.points 1 -ᵥ s.points 0) (s.points 2 -ᵥ s.points 0),
    real_inner_comm (s.points 1 -ᵥ s.points 0) (s.points 3 -ᵥ s.points 0),
    real_inner_comm (s.points 2 -ᵥ s.points 0) (s.points 3 -ᵥ s.points 0)] at h
  intro h0
  apply h
  change _ = (0 : ℝ)
  linear_combination h0

/-- **The areas of the four faces.** Four times the squared area of each face of a tetrahedron,
in terms of two edge vectors of that face: the face opposite vertex `0` from vertex `1`, the
other three from vertex `0`. -/
theorem four_mul_volume_faceOpposite_sq (s : Simplex ℝ P 3) :
    (4 * (s.faceOpposite 0).volume ^ 2 =
      ‖s.points 2 -ᵥ s.points 1‖ ^ 2 * ‖s.points 3 -ᵥ s.points 1‖ ^ 2 -
        ⟪s.points 2 -ᵥ s.points 1, s.points 3 -ᵥ s.points 1⟫ ^ 2) ∧
    (4 * (s.faceOpposite 1).volume ^ 2 =
      ‖s.points 2 -ᵥ s.points 0‖ ^ 2 * ‖s.points 3 -ᵥ s.points 0‖ ^ 2 -
        ⟪s.points 2 -ᵥ s.points 0, s.points 3 -ᵥ s.points 0⟫ ^ 2) ∧
    (4 * (s.faceOpposite 2).volume ^ 2 =
      ‖s.points 1 -ᵥ s.points 0‖ ^ 2 * ‖s.points 3 -ᵥ s.points 0‖ ^ 2 -
        ⟪s.points 1 -ᵥ s.points 0, s.points 3 -ᵥ s.points 0⟫ ^ 2) ∧
    (4 * (s.faceOpposite 3).volume ^ 2 =
      ‖s.points 1 -ᵥ s.points 0‖ ^ 2 * ‖s.points 2 -ᵥ s.points 0‖ ^ 2 -
        ⟪s.points 1 -ᵥ s.points 0, s.points 2 -ᵥ s.points 0⟫ ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Simplex.faceOpposite_point_eq_point_succAbove, Fin.succAbove] using
      four_mul_volume_sq (s.faceOpposite 0)
  · simpa [Simplex.faceOpposite_point_eq_point_succAbove, Fin.succAbove] using
      four_mul_volume_sq (s.faceOpposite 1)
  · simpa [Simplex.faceOpposite_point_eq_point_succAbove, Fin.succAbove] using
      four_mul_volume_sq (s.faceOpposite 2)
  · simpa [Simplex.faceOpposite_point_eq_point_succAbove, Fin.succAbove] using
      four_mul_volume_sq (s.faceOpposite 3)

/-- The squared distance between two points, in terms of their position vectors from a third. -/
theorem dist_sq_eq (a b o : P) :
    dist a b ^ 2 = ‖a -ᵥ o‖ ^ 2 + ‖b -ᵥ o‖ ^ 2 - 2 * ⟪a -ᵥ o, b -ᵥ o⟫ := by
  rw [dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right a b o, norm_sub_sq_real]
  ring

omit [InnerProductSpace ℝ V] in
/-- The squared distance from a point `o` to a point `a` is `‖a -ᵥ o‖²`. -/
theorem dist_sq_eq' (o a : P) : dist o a ^ 2 = ‖a -ᵥ o‖ ^ 2 := by
  rw [dist_comm, dist_eq_norm_vsub V]

/-- **Bang's theorem on equifacial tetrahedra.** If the four faces of a tetrahedron have equal
area, then opposite edges are equal in pairs. -/
theorem dist_eq_of_volume_faceOpposite_eq (s : Simplex ℝ P 3)
    (h : ∀ i j, (s.faceOpposite i).volume = (s.faceOpposite j).volume) :
    dist (s.points 0) (s.points 1) = dist (s.points 2) (s.points 3) ∧
    dist (s.points 0) (s.points 2) = dist (s.points 1) (s.points 3) ∧
    dist (s.points 0) (s.points 3) = dist (s.points 1) (s.points 2) := by
  obtain ⟨F₀, F₁, F₂, F₃⟩ := four_mul_volume_faceOpposite_sq s
  -- The face opposite vertex `0` has edge vectors `b - a` and `c - a`.
  rw [← vsub_sub_vsub_cancel_right (s.points 2) (s.points 1) (s.points 0),
    ← vsub_sub_vsub_cancel_right (s.points 3) (s.points 1) (s.points 0), norm_sub_sq_real,
    norm_sub_sq_real, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_sq,
    real_inner_comm (s.points 1 -ᵥ s.points 0) (s.points 2 -ᵥ s.points 0),
    real_inner_comm (s.points 1 -ᵥ s.points 0) (s.points 3 -ᵥ s.points 0)] at F₀
  have d₀₁ := dist_sq_eq' (s.points 0) (s.points 1)
  have d₀₂ := dist_sq_eq' (s.points 0) (s.points 2)
  have d₀₃ := dist_sq_eq' (s.points 0) (s.points 3)
  have d₂₃ := dist_sq_eq (s.points 2) (s.points 3) (s.points 0)
  have d₁₃ := dist_sq_eq (s.points 1) (s.points 3) (s.points 0)
  have d₁₂ := dist_sq_eq (s.points 1) (s.points 2) (s.points 0)
  rw [h 0 1] at F₀
  rw [h 2 1] at F₂
  rw [h 3 1] at F₃
  have hΔ := gram_det_ne_zero s
  generalize ‖s.points 1 -ᵥ s.points 0‖ ^ 2 = x at *
  generalize ‖s.points 2 -ᵥ s.points 0‖ ^ 2 = y at *
  generalize ‖s.points 3 -ᵥ s.points 0‖ ^ 2 = z at *
  generalize ⟪s.points 2 -ᵥ s.points 0, s.points 3 -ᵥ s.points 0⟫ = p at *
  generalize ⟪s.points 1 -ᵥ s.points 0, s.points 3 -ᵥ s.points 0⟫ = q at *
  generalize ⟪s.points 1 -ᵥ s.points 0, s.points 2 -ᵥ s.points 0⟫ = r at *
  have sq_inj : ∀ {u v u' v' : P}, dist u v ^ 2 = dist u' v' ^ 2 → dist u v = dist u' v' :=
    fun e ↦ (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 e
  refine ⟨sq_inj ?_, sq_inj ?_, sq_inj ?_⟩
  · rw [d₀₁, d₂₃]
    have e := eq_of_cofactor_eq (x := z) (y := y) (z := x) (p := r) (q := q) (r := p)
      (by intro h0; apply hΔ; linear_combination h0) (by linarith) (by linarith)
      (by linear_combination F₀ - F₃)
    linarith
  · rw [d₀₂, d₁₃]
    exact eq_of_cofactor_eq (x := x) (y := z) (z := y) (p := p) (q := r) (r := q)
      (by intro h0; apply hΔ; linear_combination h0) (by linarith) (by linarith)
      (by linear_combination F₀ - F₁)
  · rw [d₀₃, d₁₂]
    exact eq_of_cofactor_eq (x := x) (y := y) (z := z) (p := p) (q := q) (r := r)
      hΔ (by linarith) (by linarith) (by linear_combination F₀ - F₁)

/-- **The converse.** If opposite edges of a tetrahedron are equal in pairs, its four faces have
equal area. (They are in fact congruent; this is the easy direction.) -/
theorem volume_faceOpposite_eq_of_dist_eq (s : Simplex ℝ P 3)
    (h₁ : dist (s.points 0) (s.points 1) = dist (s.points 2) (s.points 3))
    (h₂ : dist (s.points 0) (s.points 2) = dist (s.points 1) (s.points 3))
    (h₃ : dist (s.points 0) (s.points 3) = dist (s.points 1) (s.points 2)) (i j : Fin 4) :
    (s.faceOpposite i).volume = (s.faceOpposite j).volume := by
  obtain ⟨F₀, F₁, F₂, F₃⟩ := four_mul_volume_faceOpposite_sq s
  -- The face opposite vertex `0` has edge vectors `b - a` and `c - a`.
  rw [← vsub_sub_vsub_cancel_right (s.points 2) (s.points 1) (s.points 0),
    ← vsub_sub_vsub_cancel_right (s.points 3) (s.points 1) (s.points 0), norm_sub_sq_real,
    norm_sub_sq_real, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_sq,
    real_inner_comm (s.points 1 -ᵥ s.points 0) (s.points 2 -ᵥ s.points 0),
    real_inner_comm (s.points 1 -ᵥ s.points 0) (s.points 3 -ᵥ s.points 0)] at F₀
  have d₀₁ := dist_sq_eq' (s.points 0) (s.points 1)
  have d₀₂ := dist_sq_eq' (s.points 0) (s.points 2)
  have d₀₃ := dist_sq_eq' (s.points 0) (s.points 3)
  have d₂₃ := dist_sq_eq (s.points 2) (s.points 3) (s.points 0)
  have d₁₃ := dist_sq_eq (s.points 1) (s.points 3) (s.points 0)
  have d₁₂ := dist_sq_eq (s.points 1) (s.points 2) (s.points 0)
  rw [h₁, d₂₃] at d₀₁
  rw [h₂, d₁₃] at d₀₂
  rw [h₃, d₁₂] at d₀₃
  generalize ‖s.points 1 -ᵥ s.points 0‖ ^ 2 = x at *
  generalize ‖s.points 2 -ᵥ s.points 0‖ ^ 2 = y at *
  generalize ‖s.points 3 -ᵥ s.points 0‖ ^ 2 = z at *
  generalize ⟪s.points 2 -ᵥ s.points 0, s.points 3 -ᵥ s.points 0⟫ = p at *
  generalize ⟪s.points 1 -ᵥ s.points 0, s.points 3 -ᵥ s.points 0⟫ = q at *
  generalize ⟪s.points 1 -ᵥ s.points 0, s.points 2 -ᵥ s.points 0⟫ = r at *
  have key : ∀ k : Fin 4, (s.faceOpposite k).volume = (s.faceOpposite 3).volume := by
    intro k
    refine (pow_left_inj₀ (s.faceOpposite k).volume_pos.le (s.faceOpposite 3).volume_pos.le
      two_ne_zero).1 ?_
    have hx : x = q + r := by linarith
    have hy : y = p + r := by linarith
    have hz : z = p + q := by linarith
    subst hx hy hz
    fin_cases k
    · change (s.faceOpposite 0).volume ^ 2 = _
      linear_combination (1 / 4 : ℝ) * F₀ - (1 / 4 : ℝ) * F₃
    · change (s.faceOpposite 1).volume ^ 2 = _
      linear_combination (1 / 4 : ℝ) * F₁ - (1 / 4 : ℝ) * F₃
    · change (s.faceOpposite 2).volume ^ 2 = _
      linear_combination (1 / 4 : ℝ) * F₂ - (1 / 4 : ℝ) * F₃
    · rfl
  rw [key i, key j]

/-- **Bang's theorem with its converse.** The four faces of a tetrahedron have equal area if and
only if opposite edges are equal in pairs. -/
theorem volume_faceOpposite_eq_iff_dist_eq (s : Simplex ℝ P 3) :
    (∀ i j, (s.faceOpposite i).volume = (s.faceOpposite j).volume) ↔
      dist (s.points 0) (s.points 1) = dist (s.points 2) (s.points 3) ∧
      dist (s.points 0) (s.points 2) = dist (s.points 1) (s.points 3) ∧
      dist (s.points 0) (s.points 3) = dist (s.points 1) (s.points 2) :=
  ⟨dist_eq_of_volume_faceOpposite_eq s,
    fun ⟨h₁, h₂, h₃⟩ ↦ volume_faceOpposite_eq_of_dist_eq s h₁ h₂ h₃⟩

end Bang
