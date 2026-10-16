module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicitScalar

@[expose] public section


/-!
# The transported values of the scalar form at the good-line coordinate

The Levi part `B(u)` of the plane point of the good-line argument is
`[[1 / (α R), -s t / (α R²)], [0, α / R²]]`, of determinant `R⁻³`, so the transfer scale is
`TS(u) = (√R)^{-(n+3)}`. Writing `B(u) = B'(u) · (√R)⁻³` with `B'(u)` of determinant one and
`B'(u) · i = z(u) = (i R - s t) / α²`, the analytic data of the scalar form give
`F_{h B(u)}(i) = (α / √R)^{-(n+3)} F_h(z(u))` and
`F_{h B(u) J}(i) = (α / √R)^{-(n+3)} F_{h J}(refl z(u))`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

namespace EdgeExplicit

/-! ### The Levi part of the good-line plane point -/

theorem gsPlaneVertex_standard_right_val (u : ℝ × ℝ) :
    (gsPlaneVertex (standardGoodLineRealArgument u)).right.val =
      !![1 / (gsAlpha u * gsRadius u), -(u.1 * u.2) / (gsRadius u ^ 2 * gsAlpha u);
        0, gsAlpha u / gsRadius u ^ 2] := by
  have hr := (gsRadius_pos u).ne'
  have ha := (gsAlpha_pos u).ne'
  have entry := planeNormalize_levi_val (gsUpper_mem_planeParabolic u) (gsUpper_corner_pos u)
  rw [gsPlaneVertex, gsVertex_standard]
  ext i j
  rw [entry, gsUpper_val, gsUpperMatrix]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem det_gsPlaneVertex_standard_right (u : ℝ × ℝ) :
    (gsPlaneVertex (standardGoodLineRealArgument u)).right.val.det = (gsRadius u ^ 3)⁻¹ := by
  have hr := (gsRadius_pos u).ne'
  have ha := (gsAlpha_pos u).ne'
  rw [gsPlaneVertex_standard_right_val, Matrix.det_fin_two_of]
  field_simp
  ring

/-- **The transfer scale** `TS(u) = (√R)^{-(n+3)}`. -/
theorem transferScale_eq (u : ℝ × ℝ) :
    transferScale n u = ((Real.sqrt (gsRadius u) : ℂ) ^ (n + 3))⁻¹ := by
  have hr := gsRadius_pos u
  have corner : (cornerScale (gsVertex (standardGoodLineRealArgument u)) : ℝ) =
      (gsRadius u)⁻¹ := by
    rw [gsVertex_standard, cornerScale_val (gsUpper_corner_pos u).ne', gsUpper_corner,
      abs_of_pos hr]
  have root : (Real.sqrt (gsRadius u) : ℂ) = Complex.exp ((Real.log (gsRadius u) : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
    push_cast
    ring_nf
  have radius : (gsRadius u : ℂ) = Complex.exp (Real.log (gsRadius u) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hr]
  rw [transferScale, binary_normalizingFactor_eq, det_gsPlaneVertex_standard_right, corner,
    Real.log_inv, Real.log_pow, root, Complex.ofReal_inv, inv_inv, radius,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### The unimodular Levi factor -/

/-- The determinant-one matrix `B'(u) = [[√R / α, -s t / (α √R)], [0, α / √R]]`. -/
def unimodularGoodLevi (u : ℝ × ℝ) : BinaryRealGL :=
  ⟨!![Real.sqrt (gsRadius u) / gsAlpha u, -(u.1 * u.2) / (gsAlpha u * Real.sqrt (gsRadius u));
      0, gsAlpha u / Real.sqrt (gsRadius u)],
    !![gsAlpha u / Real.sqrt (gsRadius u), u.1 * u.2 / (gsAlpha u * Real.sqrt (gsRadius u));
      0, Real.sqrt (gsRadius u) / gsAlpha u], by
    have ha := (gsAlpha_pos u).ne'
    have hq := (Real.sqrt_pos.mpr (gsRadius_pos u)).ne'
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp
    ring, by
    have ha := (gsAlpha_pos u).ne'
    have hq := (Real.sqrt_pos.mpr (gsRadius_pos u)).ne'
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp
    ring⟩

/-- The reflected determinant-one matrix `J B'(u) J`. -/
def reflectedGoodLevi (u : ℝ × ℝ) : BinaryRealGL :=
  UpperHalfPlane.J * unimodularGoodLevi u * UpperHalfPlane.J

theorem unimodularGoodLevi_val (u : ℝ × ℝ) : (unimodularGoodLevi u).val =
    !![Real.sqrt (gsRadius u) / gsAlpha u, -(u.1 * u.2) / (gsAlpha u * Real.sqrt (gsRadius u));
      0, gsAlpha u / Real.sqrt (gsRadius u)] := rfl

theorem reflectedGoodLevi_val (u : ℝ × ℝ) : (reflectedGoodLevi u).val =
    !![Real.sqrt (gsRadius u) / gsAlpha u, u.1 * u.2 / (gsAlpha u * Real.sqrt (gsRadius u));
      0, gsAlpha u / Real.sqrt (gsRadius u)] := by
  rw [reflectedGoodLevi, Units.val_mul, Units.val_mul, unimodularGoodLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two, neg_div]

theorem det_unimodularGoodLevi (u : ℝ × ℝ) : (unimodularGoodLevi u).val.det = 1 := by
  have ha := (gsAlpha_pos u).ne'
  have hq := (Real.sqrt_pos.mpr (gsRadius_pos u)).ne'
  rw [unimodularGoodLevi_val, Matrix.det_fin_two_of]
  field_simp
  ring

theorem det_reflectedGoodLevi (u : ℝ × ℝ) : (reflectedGoodLevi u).val.det = 1 := by
  rw [reflectedGoodLevi, det_upperJ_conj (det_unimodularGoodLevi u)]

/-- The positive scale `(√R)⁻³` of the Levi part. -/
def goodLeviScale (u : ℝ × ℝ) : ℝˣ :=
  Units.mk0 ((Real.sqrt (gsRadius u) ^ 3)⁻¹)
    (inv_ne_zero (pow_ne_zero 3 (Real.sqrt_pos.mpr (gsRadius_pos u)).ne'))

theorem goodLeviScale_pos (u : ℝ × ℝ) : 0 < ((goodLeviScale u : ℝˣ) : ℝ) := by
  change 0 < (Real.sqrt (gsRadius u) ^ 3)⁻¹
  have := Real.sqrt_pos.mpr (gsRadius_pos u)
  positivity

theorem sqrt_gsRadius_sq (u : ℝ × ℝ) : Real.sqrt (gsRadius u) ^ 2 = gsRadius u :=
  Real.sq_sqrt (gsRadius_pos u).le

/-- **The Levi part factors** as `B(u) = B'(u) · (√R)⁻³`. -/
theorem gsPlaneVertex_standard_right_eq (u : ℝ × ℝ) :
    (gsPlaneVertex (standardGoodLineRealArgument u)).right =
      unimodularGoodLevi u * GeneralLinearGroup.scalar (Fin 2) (goodLeviScale u) := by
  have ha := (gsAlpha_pos u).ne'
  have hq := (Real.sqrt_pos.mpr (gsRadius_pos u)).ne'
  have hr := (gsRadius_pos u).ne'
  have hsq := sqrt_gsRadius_sq u
  have hsq4 : Real.sqrt (gsRadius u) ^ 4 = gsRadius u ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  apply Units.ext
  rw [gsPlaneVertex_standard_right_val, Units.val_mul, unimodularGoodLevi_val]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [goodLeviScale, Matrix.mul_apply, Fin.sum_univ_two, GeneralLinearGroup.scalar]
  all_goals field_simp
  all_goals simp [hsq, hsq4]

theorem gsPlaneVertex_standard_right_mul_J (u : ℝ × ℝ) :
    (gsPlaneVertex (standardGoodLineRealArgument u)).right * UpperHalfPlane.J =
      UpperHalfPlane.J *
        (reflectedGoodLevi u * GeneralLinearGroup.scalar (Fin 2) (goodLeviScale u)) := by
  rw [gsPlaneVertex_standard_right_eq, reflectedGoodLevi, mul_assoc,
    GeneralLinearGroup.scalar_commute]
  simp only [← mul_assoc, upperJ_mul_self, one_mul]

/-! ### The Levi points -/

/-- The Levi point `z(u) = (i R - s t) / α²` of the good-line vertex. -/
def goodPoint (u : ℝ × ℝ) : ℂ :=
  (Complex.I * (gsRadius u : ℂ) - (u.1 : ℂ) * (u.2 : ℂ)) / (gsAlpha u : ℂ) ^ 2

theorem denom_unimodularGoodLevi (u : ℝ × ℝ) :
    UpperHalfPlane.denom (unimodularGoodLevi u) Complex.I =
      ((gsAlpha u / Real.sqrt (gsRadius u) : ℝ) : ℂ) := by
  simp [UpperHalfPlane.denom, unimodularGoodLevi_val]

theorem denom_reflectedGoodLevi (u : ℝ × ℝ) :
    UpperHalfPlane.denom (reflectedGoodLevi u) Complex.I =
      ((gsAlpha u / Real.sqrt (gsRadius u) : ℝ) : ℂ) := by
  simp [UpperHalfPlane.denom, reflectedGoodLevi_val]

theorem coe_smul_I_of_upper {A : BinaryRealGL} (hA : 0 < A.val.det) (h10 : A.val 1 0 = 0) :
    ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
      ((A.val 0 0 : ℂ) * Complex.I + (A.val 0 1 : ℂ)) / (A.val 1 1 : ℂ) := by
  rw [UpperHalfPlane.coe_smul, UpperHalfPlane.σ, ite_eq_left (by
    rw [GeneralLinearGroup.val_det_apply]; exact hA)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, h10]

theorem unimodularGoodLevi_smul_I (u : ℝ × ℝ) :
    ((unimodularGoodLevi u • UpperHalfPlane.I : UpperHalfPlane) : ℂ) = goodPoint u := by
  have ha := gsAlpha_complex_ne_zero u
  have hq : (Real.sqrt (gsRadius u) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (gsRadius_pos u)).ne'
  have hsq : (Real.sqrt (gsRadius u) : ℂ) ^ 2 = (gsRadius u : ℂ) := by
    exact_mod_cast sqrt_gsRadius_sq u
  rw [coe_smul_I_of_upper (by rw [det_unimodularGoodLevi]; exact one_pos)
    (by simp [unimodularGoodLevi_val]), goodPoint]
  simp only [unimodularGoodLevi_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  rw [← hsq]
  field_simp
  ring

theorem reflectedGoodLevi_smul_I (u : ℝ × ℝ) :
    ((reflectedGoodLevi u • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
      binaryComplexReflection (goodPoint u) := by
  have ha := gsAlpha_complex_ne_zero u
  have hq : (Real.sqrt (gsRadius u) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (gsRadius_pos u)).ne'
  have hsq : (Real.sqrt (gsRadius u) : ℂ) ^ 2 = (gsRadius u : ℂ) := by
    exact_mod_cast sqrt_gsRadius_sq u
  rw [coe_smul_I_of_upper (by rw [det_reflectedGoodLevi]; exact one_pos)
    (by simp [reflectedGoodLevi_val]), goodPoint]
  simp only [reflectedGoodLevi_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [binaryComplexReflection]
  simp only [_root_.neg_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_div₀,
    map_sub, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  rw [← hsq]
  field_simp
  ring

/-! ### Transport of the scalar form -/

section Transport

variable {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
include hF

/-- **The scalar form at the transported point**: `F_{h B(u)}(i) = (α / √R)^{-(n+3)} F_h(z(u))`. -/
theorem eichlerData_movedPoint (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    F (movedPoint u h) Complex.I =
      (((gsAlpha u / Real.sqrt (gsRadius u) : ℝ) : ℂ) ^ (n + 3))⁻¹ * F h (goodPoint u) := by
  have modular := hF.modular (unimodularGoodLevi u) (det_unimodularGoodLevi u) h
    UpperHalfPlane.I
  rw [UpperHalfPlane.coe_I, denom_unimodularGoodLevi, unimodularGoodLevi_smul_I] at modular
  rw [movedPoint, gsPlaneVertex_standard_right_eq, atInfinity_mul, ← mul_assoc,
    hF.central _ (goodLeviScale_pos u), modular, _root_.zpow_neg]
  norm_cast

/-- **The reflected scalar form at the transported point**:
`F_{h B(u) J}(i) = (α / √R)^{-(n+3)} F_{h J}(refl z(u))`. -/
theorem eichlerData_movedPoint_J (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    F (movedPoint u h * atInfinity UpperHalfPlane.J) Complex.I =
      (((gsAlpha u / Real.sqrt (gsRadius u) : ℝ) : ℂ) ^ (n + 3))⁻¹ *
        F (h * atInfinity UpperHalfPlane.J) (binaryComplexReflection (goodPoint u)) := by
  have modular := hF.modular (reflectedGoodLevi u) (det_reflectedGoodLevi u)
    (h * atInfinity UpperHalfPlane.J) UpperHalfPlane.I
  rw [UpperHalfPlane.coe_I, denom_reflectedGoodLevi, reflectedGoodLevi_smul_I] at modular
  rw [movedPoint, mul_assoc, ← atInfinity_mul, gsPlaneVertex_standard_right_mul_J,
    atInfinity_mul, atInfinity_mul, ← mul_assoc, ← mul_assoc, hF.central _ (goodLeviScale_pos u),
    modular, _root_.zpow_neg]
  norm_cast

end Transport

end EdgeExplicit

end TernaryPeriodPolynomials.AnalyticClasses
