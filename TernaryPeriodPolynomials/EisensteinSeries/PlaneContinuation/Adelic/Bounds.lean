module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.Level
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.LatticeBounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RowAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicBounds

theorem norm_planeCuspVector_real_finite {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (realMatrix : RealGL3) (finiteMatrix : FiniteGL)
    (parabolicElement : planeParabolic ℝ) (orthogonalElement : RealGL3)
    (factorization : realMatrix = parabolicElement.val * orthogonalElement)
    (orthogonality : orthogonalElement.val.transpose * orthogonalElement.val = 1)
    (cornerValue : (planeCornerUnit parabolicElement).val =
      ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
        EuclideanSpace ℝ (Fin 3))‖) :
    ‖(planeCuspVector inducedSection
      (atInfinity realMatrix * atFinite finiteMatrix)).val‖ =
      Real.exp ((((degree : ℝ) + 4) / 2 + parameter.re / 3) *
          Real.log |realMatrix.val.det| -
        (parameter.re + ((degree : ℝ) + 6) / 2) *
          Real.log ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
            EuclideanSpace ℝ (Fin 3))‖) *
        ‖(planeCuspVector inducedSection
          (atInfinity orthogonalElement * atFinite finiteMatrix)).val‖ := by
  have embeddedFactorization : atInfinity realMatrix =
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.planeParabolicAtInfinity parabolicElement).val *
        atInfinity orthogonalElement := by
    rw [factorization, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
    rfl
  rw [embeddedFactorization, mul_assoc, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Bounds.norm_planeCuspVector_planeParabolic,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.corner_atInfinity, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.binaryBlock_atInfinity,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_real, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_atInfinity]
  have heightFormula := TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.real_heightLog_formula realMatrix
    parabolicElement orthogonalElement factorization orthogonality cornerValue
  rw [cornerValue, abs_of_nonneg (norm_nonneg _)] at heightFormula ⊢
  have binaryLog : Real.log |(planeBinaryBlock parabolicElement).val.det| =
      Real.log |realMatrix.val.det| -
        Real.log ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
          EuclideanSpace ℝ (Fin 3))‖ := by
    linarith
  rw [binaryLog]
  congr 2
  norm_num [binaryInductionExponent, inductionExponent, Complex.mul_re]
  ring

theorem flatSection_real_integral_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ realMatrix : RealGL3,
      ∀ integralMatrix : IntegralGL3,
      ‖(planeCuspVector (flatSection.1 parameter)
        (atInfinity realMatrix * atFinite (integralFinite integralMatrix))).val‖ ≤
        |realMatrix.val.det| ^ (((degree : ℝ) + 4) / 2 + parameter.re / 3) *
          ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
            EuclideanSpace ℝ (Fin 3))‖ ^ (-(parameter.re + ((degree : ℝ) + 6) / 2)) * bound := by
  obtain ⟨bound, nonnegativeBound, compactBound⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.flatSection_compact_cuspVector_bound flatSection
  refine ⟨bound, nonnegativeBound, fun parameter realMatrix integralMatrix => ?_⟩
  obtain ⟨parabolicElement, orthogonalElement, factorization, orthogonality, cornerValue⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.exists_plane_orthogonal realMatrix
  rw [norm_planeCuspVector_real_finite (flatSection.1 parameter) realMatrix _ parabolicElement
    orthogonalElement factorization orthogonality cornerValue,
    Real.rpow_def_of_pos (abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero realMatrix)),
    Real.rpow_def_of_pos (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Bounds.lastRow_norm_pos realMatrix), ← Real.exp_add]
  have exponentEquality :
      Real.log |realMatrix.val.det| * (((degree : ℝ) + 4) / 2 + parameter.re / 3) +
        Real.log ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
          EuclideanSpace ℝ (Fin 3))‖ * (-(parameter.re + ((degree : ℝ) + 6) / 2)) =
      (((degree : ℝ) + 4) / 2 + parameter.re / 3) * Real.log |realMatrix.val.det| -
        (parameter.re + ((degree : ℝ) + 6) / 2) *
          Real.log ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
            EuclideanSpace ℝ (Fin 3))‖ := by ring
  rw [exponentEquality]
  exact mul_le_mul_of_nonneg_left
    (compactBound parameter orthogonalElement orthogonality integralMatrix) (Real.exp_pos _).le

theorem norm_planeCuspVector_rational_plane {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (element : planeParabolic ℚ) (basePoint : AdelicGL) :
    ‖(planeCuspVector inducedSection (rationalGroup element.val * basePoint)).val‖ =
      ‖(planeCuspVector inducedSection basePoint).val‖ := by
  have normFormula := TernaryPeriodPolynomials.PlaneEisensteinContinuation.Bounds.norm_planeCuspVector_planeParabolic inducedSection
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.rationalPlane element) basePoint
  have cornerNorm : adeleNorm (planeCornerUnit
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.rationalPlane element)) = 1 := by
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.corner_rational]
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductFormula.adeleNorm_rational _
  have binaryNorm : adeleNorm (Matrix.GeneralLinearGroup.det (planeBinaryBlock
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.rationalPlane element))) = 1 := by
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.binaryBlock_rational, Matrix.GeneralLinearGroup.map_det]
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductFormula.adeleNorm_rational _
  rw [cornerNorm, binaryNorm, NNReal.coe_one, Real.log_one, mul_zero,
    mul_zero, add_zero, Real.exp_zero, one_mul] at normFormula
  exact normFormula

theorem norm_planeCuspVector_eq_of_flag {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (first second : RationalGL3)
    (sameFlag : (QuotientGroup.mk first : Flags .plane) = QuotientGroup.mk second)
    (basePoint : AdelicGL) :
    ‖(planeCuspVector inducedSection (rationalGroup first⁻¹ * basePoint)).val‖ =
      ‖(planeCuspVector inducedSection (rationalGroup second⁻¹ * basePoint)).val‖ := by
  have parabolicMembership : first⁻¹ * second ∈ planeParabolic ℚ := QuotientGroup.eq.mp sameFlag
  have invariance := norm_planeCuspVector_rational_plane inducedSection
    ⟨first⁻¹ * second, parabolicMembership⟩ (rationalGroup second⁻¹ * basePoint)
  change ‖(planeCuspVector inducedSection (rationalGroup (first⁻¹ * second) *
    (rationalGroup second⁻¹ * basePoint))).val‖ = _ at invariance
  rw [← mul_assoc, ← map_mul, mul_inv_cancel_right] at invariance
  exact invariance

theorem flatSection_integral_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ integralMatrix : IntegralGL3,
      ‖(planeCuspVector (flatSection.1 parameter)
        (rationalGroup (integralRational integralMatrix))).val‖ ≤
        ‖(WithLp.toLp 2 (fun column : Fin 3 => (integralMatrix.val 2 column : ℝ)) :
          EuclideanSpace ℝ (Fin 3))‖ ^ (-(parameter.re + ((degree : ℝ) + 6) / 2)) * bound := by
  obtain ⟨bound, nonnegativeBound, realBound⟩ := flatSection_real_integral_bound flatSection
  refine ⟨bound, nonnegativeBound, fun parameter integralMatrix => ?_⟩
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralGroup_eq_mul]
  have matrixBound := realBound parameter
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) integralMatrix) integralMatrix
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.abs_det_integral_real, Real.one_rpow, one_mul] at matrixBound
  exact matrixBound

theorem flatSection_flag_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ flag : Flags .plane,
      ‖(planeCuspVector (flatSection.1 parameter) (rationalGroup flag.out⁻¹)).val‖ ≤
        ‖(WithLp.toLp 2 (fun column : Fin 3 =>
          (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)) :
            EuclideanSpace ℝ (Fin 3))‖ ^ (-(parameter.re + ((degree : ℝ) + 6) / 2)) * bound := by
  obtain ⟨bound, nonnegativeBound, integralBound⟩ := flatSection_integral_bound flatSection
  refine ⟨bound, nonnegativeBound, fun parameter flag => ?_⟩
  have sameFlag : (QuotientGroup.mk flag.out : Flags .plane) = QuotientGroup.mk
      (integralRational (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)) := by
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative_mk]
    exact Quotient.out_eq flag
  have normEquality := norm_planeCuspVector_eq_of_flag (flatSection.1 parameter) _ _ sameFlag 1
  simp only [mul_one] at normEquality
  rw [normEquality, ← map_inv]
  exact integralBound parameter (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹

theorem summable_norm_flag_cuspVectors {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (fun flag : Flags .plane =>
      ‖(planeCuspVector (flatSection.1 parameter) (rationalGroup flag.out⁻¹)).val‖) := by
  obtain ⟨bound, _, flagBound⟩ := flatSection_flag_bound flatSection
  have rowSummable := TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.summable_integralFlagRow_rpow
    (-(parameter.re + ((degree : ℝ) + 6) / 2)) (by linarith)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (flagBound parameter)
    (rowSummable.mul_right bound)

theorem summable_flag_cuspVectors {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (fun flag : Flags .plane =>
      (planeCuspVector (flatSection.1 parameter) (rationalGroup flag.out⁻¹)).val) :=
  (summable_norm_flag_cuspVectors flatSection parameter rightHalfPlane).of_norm

theorem flatSection_integral_real_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ realMatrix : RealGL3,
      ∀ integralMatrix : IntegralGL3,
      ‖(planeCuspVector (flatSection.1 parameter)
        (rationalGroup (integralRational integralMatrix) * atInfinity realMatrix)).val‖ ≤
        |realMatrix.val.det| ^ (((degree : ℝ) + 4) / 2 + parameter.re / 3) *
          ‖(WithLp.toLp 2 ((fun column : Fin 3 => (integralMatrix.val 2 column : ℝ)) ᵥ*
            realMatrix.val) : EuclideanSpace ℝ (Fin 3))‖ ^
              (-(parameter.re + ((degree : ℝ) + 6) / 2)) * bound := by
  obtain ⟨bound, nonnegativeBound, realBound⟩ := flatSection_real_integral_bound flatSection
  refine ⟨bound, nonnegativeBound, fun parameter realMatrix integralMatrix => ?_⟩
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralGroup_eq_mul, mul_assoc,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute, ← mul_assoc,
    ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
  have matrixBound := realBound parameter
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) integralMatrix * realMatrix) integralMatrix
  rw [Units.val_mul, Matrix.det_mul, abs_mul,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.abs_det_integral_real, one_mul] at matrixBound
  exact matrixBound

theorem flatSection_flag_real_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ realMatrix : RealGL3,
      ∀ flag : Flags .plane,
      ‖(planeCuspVector (flatSection.1 parameter)
        (rationalGroup flag.out⁻¹ * atInfinity realMatrix)).val‖ ≤
        |realMatrix.val.det| ^ (((degree : ℝ) + 4) / 2 + parameter.re / 3) *
          ‖(WithLp.toLp 2 ((fun column : Fin 3 =>
            (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)) ᵥ*
              realMatrix.val) : EuclideanSpace ℝ (Fin 3))‖ ^
                (-(parameter.re + ((degree : ℝ) + 6) / 2)) * bound := by
  obtain ⟨bound, nonnegativeBound, integralBound⟩ := flatSection_integral_real_bound flatSection
  refine ⟨bound, nonnegativeBound, fun parameter realMatrix flag => ?_⟩
  have sameFlag : (QuotientGroup.mk flag.out : Flags .plane) = QuotientGroup.mk
      (integralRational (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)) := by
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative_mk]
    exact Quotient.out_eq flag
  rw [norm_planeCuspVector_eq_of_flag (flatSection.1 parameter) _ _ sameFlag, ← map_inv]
  exact integralBound parameter realMatrix
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹

theorem summable_norm_flag_cuspVectors_atInfinity {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (fun flag : Flags .plane =>
      ‖(planeCuspVector (flatSection.1 parameter)
        (rationalGroup flag.out⁻¹ * atInfinity realMatrix)).val‖) := by
  obtain ⟨bound, _, flagBound⟩ := flatSection_flag_real_bound flatSection
  have rowSummable := TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowAction.summable_flag_row_products realMatrix
    (-(parameter.re + ((degree : ℝ) + 6) / 2)) (by linarith)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (flagBound parameter realMatrix)
    ((rowSummable.mul_left
      (|realMatrix.val.det| ^ (((degree : ℝ) + 4) / 2 + parameter.re / 3))).mul_right bound)

theorem summable_flag_cuspVectors_atInfinity {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (fun flag : Flags .plane =>
      (planeCuspVector (flatSection.1 parameter)
        (rationalGroup flag.out⁻¹ * atInfinity realMatrix)).val) :=
  (summable_norm_flag_cuspVectors_atInfinity flatSection realMatrix parameter rightHalfPlane).of_norm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicBounds
