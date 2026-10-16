module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.Height

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalBounds

theorem adeleNorm_det_parabolicPart (matrix : AdelicGL) :
    (adeleNorm (GeneralLinearGroup.det (parabolicPart matrix).val) : ℝ) =
      (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) := by
  have equality := congrArg (fun value : AdelicGL =>
    (adeleNorm (GeneralLinearGroup.det value) : ℝ)) (parabolicPart_mul_compactPart matrix)
  rw [map_mul, map_mul, NNReal.coe_mul,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.adeleNorm_det_maximalCompact _ (compactPart_mem matrix), mul_one] at equality
  exact equality.symm

theorem parabolic_exponent_eq (degree : ℕ) (parameter : ℂ) (matrix : AdelicGL) :
    (-2 * inductionExponent .plane parameter).re *
        Real.log (adeleNorm (planeCornerUnit (parabolicPart matrix)) : ℝ) +
      (binaryInductionExponent degree .plane parameter).re *
        Real.log (adeleNorm (GeneralLinearGroup.det (planeBinaryBlock (parabolicPart matrix))) : ℝ) =
    ((degree : ℝ) + 3) / 3 * Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) +
      (parameter.re + ((degree : ℝ) + 6) / 2) * height matrix := by
  rw [← adeleNorm_det_parabolicPart, det_planeParabolic, TernaryPeriodPolynomials.PlaneEisensteinContinuation.HeightProperties.log_adeleNorm_mul]
  dsimp only [height, planeHeightLog]
  norm_num [binaryInductionExponent, inductionExponent, Complex.mul_re]
  ring

theorem flatSection_height_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ matrix : AdelicGL,
      ‖(planeCuspVector (flatSection.1 parameter) matrix).val‖ ≤
        Real.exp (((degree : ℝ) + 3) / 3 * Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) +
          (parameter.re + ((degree : ℝ) + 6) / 2) * height matrix) * bound := by
  obtain ⟨bound, nonnegativeBound, boundProperty⟩ := flatSection_cuspVector_bound flatSection
  refine ⟨bound, nonnegativeBound, fun parameter matrix => ?_⟩
  simpa only [parabolic_exponent_eq] using boundProperty parameter matrix

theorem adeleNorm_det_rational_mul (rationalMatrix : RationalGL3) (basePoint : AdelicGL) :
    (adeleNorm (GeneralLinearGroup.det (rationalGroup rationalMatrix * basePoint)) : ℝ) =
      (adeleNorm (GeneralLinearGroup.det basePoint) : ℝ) := by
  have rationalNorm : adeleNorm (GeneralLinearGroup.det (rationalGroup rationalMatrix)) = 1 := by
    change adeleNorm (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rationalMatrix)) = 1
    rw [GeneralLinearGroup.map_det]
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductFormula.adeleNorm_rational _
  rw [map_mul, map_mul, rationalNorm, one_mul]

theorem summable_norm_of_height_bound {Target : Type*} [SeminormedAddCommGroup Target]
    (basePoint : AdelicGL) (values : Flags .plane → Target)
    (exponent constant compactBound : ℝ) (exponentBound : 3 < exponent)
    (nonnegativeCompactBound : 0 ≤ compactBound)
    (normBound : ∀ flag, ‖values flag‖ ≤
      Real.exp (constant + exponent * height (rationalGroup flag.out⁻¹ * basePoint)) * compactBound) :
    Summable (fun flag => ‖values flag‖) := by
  obtain ⟨finiteBound, heightBound⟩ := TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicHeight.height_flag_bound basePoint
  have positiveExponent : 0 ≤ exponent := by linarith
  let constantTerm : ℝ := constant + exponent *
    (Real.log |(realGroup basePoint).val.det| / 3 + finiteBound)
  have rowSummable := TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowAction.summable_flag_row_products (realGroup basePoint)
    (-exponent) (by linarith)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (rowSummable.mul_right (Real.exp constantTerm * compactBound))
  intro flag
  have rowPositive : 0 <
      ‖(WithLp.toLp 2 ((fun column => (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)) ᵥ*
        (realGroup basePoint).val) : EuclideanSpace ℝ (Fin 3))‖ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Bounds.lastRow_norm_pos
      (GeneralLinearGroup.map (Int.castRingHom ℝ)
        (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹ * realGroup basePoint)
  calc
    ‖values flag‖ ≤ Real.exp (constant + exponent * height (rationalGroup flag.out⁻¹ * basePoint)) *
          compactBound := normBound flag
    _ ≤ Real.exp (constant + exponent *
          (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarParameter.flagHeight (realGroup basePoint) flag + finiteBound)) * compactBound := by
      apply mul_le_mul_of_nonneg_right _ nonnegativeCompactBound
      apply Real.exp_le_exp.mpr
      exact add_le_add_right (mul_le_mul_of_nonneg_left (heightBound flag) positiveExponent) _
    _ = _ := by
      rw [Real.rpow_def_of_pos rowPositive, ← mul_assoc, ← Real.exp_add]
      congr 2
      dsimp only [constantTerm, TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarParameter.flagHeight]
      ring

theorem summable_norm_flag_cuspVectors {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (fun flag : Flags .plane =>
      ‖(planeCuspVector (flatSection.1 parameter) (rationalGroup flag.out⁻¹ * basePoint)).val‖) := by
  obtain ⟨compactBound, nonnegativeCompactBound, normBound⟩ := flatSection_height_bound flatSection
  apply summable_norm_of_height_bound basePoint _
    (parameter.re + ((degree : ℝ) + 6) / 2)
    (((degree : ℝ) + 3) / 3 * Real.log (adeleNorm (GeneralLinearGroup.det basePoint) : ℝ))
    compactBound (by linarith) nonnegativeCompactBound
  intro flag
  have boundProperty := normBound parameter (rationalGroup flag.out⁻¹ * basePoint)
  rwa [adeleNorm_det_rational_mul] at boundProperty

theorem summable_flag_cuspVectors {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (fun flag : Flags .plane =>
      (planeCuspVector (flatSection.1 parameter) (rationalGroup flag.out⁻¹ * basePoint)).val) :=
  (summable_norm_flag_cuspVectors flatSection basePoint parameter rightHalfPlane).of_norm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalBounds
