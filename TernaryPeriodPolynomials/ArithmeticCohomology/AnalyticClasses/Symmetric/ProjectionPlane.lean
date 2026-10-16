module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Symmetric.ProjectionSmooth
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LinePlaneSimplices

@[expose] public section


/-!
# The symmetric projection and the Gram–Schmidt plane vertex

For `A ∈ GL₂(ℝ)` the point `A · i` of the upper half plane is `positivePoint (A Aᵀ)`, for either
sign of `det A`. A plane-parabolic matrix `p` with positive corner is `p₂₂ · [[B, x], [0, 1]]`,
where `x` and `B` are the radical and Levi parts of `planeNormalize p`, so its Gram matrix is
`p₂₂² · [[B Bᵀ + x xᵀ, x], [xᵀ, 1]]`: the radical coordinate of `p` is `x` and its Schur complement
is `p₂₂² · B Bᵀ`, whose point is `B · i`. The Gram–Schmidt vertex of `y` with `y₂₂ > 0` is such a
matrix and has the Gram matrix of `y`, so the real-plane point of the Gram–Schmidt vertex is
given by `symmetricRadical y` and `symmetricPoint y`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- **The Möbius action on `i` through the Gram matrix.** For every `A ∈ GL₂(ℝ)` (of either
determinant sign, the action for `det A < 0` being `z ↦ A · z̄`) the point `A · i` is
`((A Aᵀ)₀₁ + i |det A|) / (A Aᵀ)₁₁`. -/
theorem coe_smul_I_eq_positivePoint (A : GL (Fin 2) ℝ) :
    ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) = positivePoint (A.val * A.valᵀ) := by
  rw [UpperHalfPlane.coe_smul, UpperHalfPlane.coe_I]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, UpperHalfPlane.σ]
  have hdet : (A.val * A.valᵀ).det = A.val.det ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose, sq]
  have hne : A.val.det ≠ 0 := A.isUnit.map Matrix.detMonoidHom |>.ne_zero
  rw [positivePoint, hdet, Real.sqrt_sq_eq_abs]
  set a := A.val 0 0
  set b := A.val 0 1
  set c := A.val 1 0
  set d := A.val 1 1
  have e01 : (A.val * A.valᵀ) 0 1 = a * c + b * d := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, a, b, c, d]
  have e11 : (A.val * A.valᵀ) 1 1 = c ^ 2 + d ^ 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, c, d, sq]
  have edet : A.val.det = a * d - b * c := by
    rw [Matrix.det_fin_two]
  rw [e01, e11]
  have hcd : c ^ 2 + d ^ 2 ≠ 0 := by
    intro h
    have hc : c = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    have hd : d = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    apply hne
    rw [edet, hc, hd]; ring
  have hden : (c : ℂ) * Complex.I + (d : ℂ) ≠ 0 := by
    intro h
    have hre : d = 0 := by simpa using congrArg Complex.re h
    have him : c = 0 := by simpa using congrArg Complex.im h
    apply hcd
    rw [hre, him]
    ring
  have hden' : (c : ℂ) * (starRingEnd ℂ Complex.I) + (d : ℂ) ≠ 0 := by
    intro h
    have hre : d = 0 := by simpa using congrArg Complex.re h
    have him : c = 0 := by simpa using congrArg Complex.im h
    apply hcd
    rw [hre, him]
    ring
  have hcd' : ((c ^ 2 + d ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcd
  rw [Matrix.GeneralLinearGroup.val_det_apply, edet]
  split_ifs with h
  · rw [abs_of_pos h, ContinuousAlgEquiv.refl_apply, div_eq_div_iff hden hcd']
    apply Complex.ext <;> simp [sq] <;> ring
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) (edet ▸ hne)), Complex.conjCAE_apply, map_div₀]
    simp only [map_add, map_mul, Complex.conj_ofReal]
    rw [div_eq_div_iff hden' hcd']
    apply Complex.ext <;> simp [sq] <;> ring

/-! ### Plane-parabolic matrices -/

theorem planeNormalize_radical {p : RealGL3} (hp : p ∈ planeParabolic ℝ)
    (positive : 0 < p.val 2 2) (i : Fin 2) :
    (planeNormalize p).left.toAdd i = p.val i.castSucc 2 / p.val 2 2 := by
  have scale := cornerScale_val positive.ne'
  rw [abs_of_pos positive] at scale
  rw [← realPlaneMatrix_radical_entry, realPlaneMatrix_planeNormalize hp positive,
    scalar_mul_val_apply, scale, inv_mul_eq_div]

theorem planeNormalize_levi_val {p : RealGL3} (hp : p ∈ planeParabolic ℝ)
    (positive : 0 < p.val 2 2) (i j : Fin 2) :
    (planeNormalize p).right.val i j = p.val i.castSucc j.castSucc / p.val 2 2 := by
  have scale := cornerScale_val positive.ne'
  rw [abs_of_pos positive] at scale
  rw [← realPlaneMatrix_binary_entry, realPlaneMatrix_planeNormalize hp positive,
    scalar_mul_val_apply, scale, inv_mul_eq_div]

/-- The radical coordinate of a plane-parabolic matrix with positive corner is the radical part
of its real-plane point. -/
theorem symmetricRadical_planeParabolic {p : RealGL3} (hp : p ∈ planeParabolic ℝ)
    (positive : 0 < p.val 2 2) :
    symmetricRadical p.val = (planeNormalize p).left.toAdd := by
  have h20 : p.val 2 0 = 0 := hp.1
  have h21 : p.val 2 1 = 0 := hp.2
  funext i
  rw [planeNormalize_radical hp positive]
  simp only [symmetricRadical, gramMatrix_apply, Fin.sum_univ_three, h20, h21]
  field_simp
  ring

/-- The Schur complement of the Gram matrix of a plane-parabolic matrix with positive corner is
`p₂₂² · B Bᵀ`, `B` the Levi part of its real-plane point. -/
theorem symmetricSchur_planeParabolic {p : RealGL3} (hp : p ∈ planeParabolic ℝ)
    (positive : 0 < p.val 2 2) :
    symmetricSchur p.val =
      (p.val 2 2 ^ 2) • ((planeNormalize p).right.val * (planeNormalize p).right.valᵀ) := by
  have h20 : p.val 2 0 = 0 := hp.1
  have h21 : p.val 2 1 = 0 := hp.2
  have levi := planeNormalize_levi_val hp positive
  funext i j
  simp only [symmetricSchur, gramMatrix_apply, Fin.sum_univ_three, h20, h21, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, levi, smul_eq_mul]
  field_simp
  simp only [Fin.isValue, Fin.castSucc_zero, Fin.castSucc_one]
  ring

/-- The Levi point of a plane-parabolic matrix with positive corner is the point of the upper half
plane given by the Levi part of its real-plane point. -/
theorem symmetricPoint_planeParabolic {p : RealGL3} (hp : p ∈ planeParabolic ℝ)
    (positive : 0 < p.val 2 2) :
    symmetricPoint p.val =
      (((planeNormalize p).right • UpperHalfPlane.I : UpperHalfPlane) : ℂ) := by
  rw [coe_smul_I_eq_positivePoint, symmetricPoint, symmetricSchur_planeParabolic hp positive,
    positivePoint_smul (by positivity)]

/-! ### The Gram–Schmidt vertex -/

theorem gsVertex_val (y : RealGL3) :
    (gsVertex y).val = y.val * ((gsOrth (gsChart y))⁻¹).val := by
  rw [gsVertex, Units.val_mul]

theorem gramMatrix_gsVertex (y : RealGL3) : gramMatrix (gsVertex y).val = gramMatrix y.val := by
  rw [gsVertex_val, gramMatrix_mul_orthogonal _ (gsOrth_inv_orthogonal _)]

theorem gsVertex_last_row (y : RealGL3) (j : Fin 3) :
    (gsVertex y).val 2 j = ∑ m, y.val 2 m * gsOrthMatrix (gsChart y) j m := by
  rw [gsVertex_val]
  change (y.val * (gsOrthMatrix (gsChart y))ᵀ) 2 j = _
  simp only [Matrix.mul_apply, Matrix.transpose_apply]

/-- For `y₂₂ > 0` the Gram–Schmidt vertex lies in the plane parabolic. -/
theorem gsVertex_mem_planeParabolic {y : RealGL3} (positive : 0 < y.val 2 2) :
    gsVertex y ∈ planeParabolic ℝ ∧ 0 < (gsVertex y).val 2 2 := by
  have hy := positive.ne'
  set u := gsChart y with hu
  have ha := (gsAlpha_pos u).ne'
  have hr := gsRadius_pos u
  have ha2 := gsAlpha_sq u
  have hr2 := gsRadius_sq u
  have e0 : y.val 2 0 = y.val 2 2 * u.2 := by
    rw [hu, gsChart]; field_simp
  have e1 : y.val 2 1 = y.val 2 2 * u.1 := by
    rw [hu, gsChart]; field_simp
  have row := gsVertex_last_row y
  rw [← hu] at row
  have k00 : gsOrthMatrix u 0 0 = 0 := by simp [gsOrthMatrix]
  have k01 : gsOrthMatrix u 0 1 = 1 / gsAlpha u := by simp [gsOrthMatrix]
  have k02 : gsOrthMatrix u 0 2 = -u.1 / gsAlpha u := by simp [gsOrthMatrix]
  have k10 : gsOrthMatrix u 1 0 = gsAlpha u / gsRadius u := by simp [gsOrthMatrix]
  have k11 : gsOrthMatrix u 1 1 = -(u.1 * u.2) / (gsRadius u * gsAlpha u) := by
    simp [gsOrthMatrix]
  have k12 : gsOrthMatrix u 1 2 = -u.2 / (gsRadius u * gsAlpha u) := by simp [gsOrthMatrix]
  have k20 : gsOrthMatrix u 2 0 = u.2 / gsRadius u := by simp [gsOrthMatrix]
  have k21 : gsOrthMatrix u 2 1 = u.1 / gsRadius u := by simp [gsOrthMatrix]
  have k22 : gsOrthMatrix u 2 2 = 1 / gsRadius u := by simp [gsOrthMatrix]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change (gsVertex y).val 2 0 = 0
    rw [row, Fin.sum_univ_three, e0, e1, k00, k01, k02]
    field_simp
    ring
  · change (gsVertex y).val 2 1 = 0
    rw [row, Fin.sum_univ_three, e0, e1, k10, k11, k12]
    field_simp
    linear_combination y.val 2 2 * u.2 * ha2
  · have key : (gsVertex y).val 2 2 = y.val 2 2 * gsRadius u := by
      rw [row, Fin.sum_univ_three, e0, e1, k20, k21, k22]
      field_simp
      linear_combination -hr2
    rw [key]
    exact mul_pos positive hr

/-- **The radical part of the Gram–Schmidt plane vertex is the symmetric radical coordinate.** -/
theorem gsPlaneVertex_radical {y : RealGL3} (positive : 0 < y.val 2 2) :
    (gsPlaneVertex y).left.toAdd = symmetricRadical y.val := by
  obtain ⟨hp, hpos⟩ := gsVertex_mem_planeParabolic positive
  rw [gsPlaneVertex, ← symmetricRadical_planeParabolic hp hpos, symmetricRadical_eq_radicalOf,
    symmetricRadical_eq_radicalOf, gramMatrix_gsVertex]

/-- **The Levi part of the Gram–Schmidt plane vertex moves `i` to the symmetric Levi point.** -/
theorem gsPlaneVertex_point {y : RealGL3} (positive : 0 < y.val 2 2) :
    (((gsPlaneVertex y).right • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
      symmetricPoint y.val := by
  obtain ⟨hp, hpos⟩ := gsVertex_mem_planeParabolic positive
  rw [gsPlaneVertex, ← symmetricPoint_planeParabolic hp hpos, symmetricPoint_eq,
    symmetricPoint_eq, gramMatrix_gsVertex]

end TernaryPeriodPolynomials.AnalyticClasses
