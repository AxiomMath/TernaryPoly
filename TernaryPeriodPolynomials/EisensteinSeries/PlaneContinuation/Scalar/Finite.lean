module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.SupNorm
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.Series

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarFinite

theorem cuspSupNorm_planeParabolic {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (parabolicElement : planeParabolic Adeles) (basePoint : AdelicGL) :
    cuspSupNorm (planeCuspVector inducedSection (parabolicElement.val * basePoint)) =
      Real.exp ((-2 * inductionExponent .plane parameter).re *
          Real.log (adeleNorm (planeCornerUnit parabolicElement) : ℝ) +
        (binaryInductionExponent degree .plane parameter).re *
          Real.log (adeleNorm
            (GeneralLinearGroup.det (planeBinaryBlock parabolicElement)) : ℝ)) *
        cuspSupNorm (planeCuspVector inducedSection basePoint) := by
  rw [planeCuspVector_planeParabolic, cuspSupNorm_smul, cuspSupNorm_smul,
    cuspSupNorm_translate, norm_mul, data.chi.unitary, one_mul,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.norm_normPower, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.norm_normPower,
    Real.exp_add, mul_assoc]

theorem cuspSupNorm_comparison_planeParabolic {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (parabolicElement : planeParabolic Adeles) (basePoint : AdelicGL) (bound : ℝ)
    (comparison : cuspSupNorm (planeCuspVector inducedSection basePoint) ≤
      bound * ‖(planeCuspVector inducedSection basePoint).val‖) :
    cuspSupNorm (planeCuspVector inducedSection (parabolicElement.val * basePoint)) ≤
      bound * ‖(planeCuspVector inducedSection (parabolicElement.val * basePoint)).val‖ := by
  rw [cuspSupNorm_planeParabolic, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Bounds.norm_planeCuspVector_planeParabolic,
    mul_left_comm bound]
  exact mul_le_mul_of_nonneg_left comparison (Real.exp_pos _).le

theorem finiteDimensional_integral_real_comparison {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (subspace : Submodule ℂ data.cusp.smooth) [FiniteDimensional ℂ subspace]
    (compactValues : ∀ realMatrix : RealGL3,
      realMatrix.val.transpose * realMatrix.val = 1 → ∀ integralMatrix : IntegralGL3,
      planeCuspVector (flatSection.1 cohomologicalPoint)
        (atInfinity realMatrix * atFinite (integralFinite integralMatrix)) ∈ subspace) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ realMatrix : RealGL3,
      ∀ integralMatrix : IntegralGL3,
      ‖sectionFamily parameter
        (rationalGroup (integralRational integralMatrix) * atInfinity realMatrix)‖ ≤
      bound * ‖(planeCuspVector (flatSection.1 parameter)
        (rationalGroup (integralRational integralMatrix) * atInfinity realMatrix)).val‖ := by
  obtain ⟨bound, nonnegativeBound, subspaceBound⟩ := finiteDimensional_cuspSupNorm_bound subspace
  refine ⟨bound, nonnegativeBound, fun parameter realMatrix integralMatrix => ?_⟩
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralGroup_eq_mul, mul_assoc,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute, ← mul_assoc,
    ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
  let realProduct := GeneralLinearGroup.map (Int.castRingHom ℝ) integralMatrix * realMatrix
  obtain ⟨parabolicElement, orthogonalElement, factorization, orthogonality, _⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.exists_plane_orthogonal realProduct
  have embeddedFactorization : atInfinity realProduct =
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.planeParabolicAtInfinity parabolicElement).val *
        atInfinity orthogonalElement := by
    rw [factorization, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
    rfl
  change ‖sectionFamily parameter (atInfinity realProduct * _)‖ ≤ _
  rw [embeddedFactorization, mul_assoc]
  rw [induced_eq_planeCuspVector_one (flatSection.1 parameter)]
  apply (realize_le_cuspSupNorm _ 1).trans
  apply cuspSupNorm_comparison_planeParabolic
  rw [flatSection_planeCuspVector_eq flatSection parameter _
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.orthogonal_integral_compact orthogonalElement orthogonality
      integralMatrix)]
  exact subspaceBound _ (compactValues orthogonalElement orthogonality integralMatrix)

theorem finiteDimensional_flag_real_comparison {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (subspace : Submodule ℂ data.cusp.smooth) [FiniteDimensional ℂ subspace]
    (compactValues : ∀ realMatrix : RealGL3,
      realMatrix.val.transpose * realMatrix.val = 1 → ∀ integralMatrix : IntegralGL3,
      planeCuspVector (flatSection.1 cohomologicalPoint)
        (atInfinity realMatrix * atFinite (integralFinite integralMatrix)) ∈ subspace) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ realMatrix : RealGL3,
      ∀ flag : Flags .plane,
      ‖eisensteinSummand sectionFamily parameter (atInfinity realMatrix) flag‖ ≤
      bound * ‖(planeCuspVector (flatSection.1 parameter)
        (rationalGroup flag.out⁻¹ * atInfinity realMatrix)).val‖ := by
  obtain ⟨bound, nonnegativeBound, integralBound⟩ :=
    finiteDimensional_integral_real_comparison flatSection subspace compactValues
  refine ⟨bound, nonnegativeBound, fun parameter realMatrix flag => ?_⟩
  have sameFlag : (QuotientGroup.mk flag.out : Flags .plane) = QuotientGroup.mk
      (integralRational (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)) := by
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative_mk]
    exact Quotient.out_eq flag
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.eisensteinSummand_eq_integral (flatSection.1 parameter),
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicBounds.norm_planeCuspVector_eq_of_flag (flatSection.1 parameter)
      _ _ sameFlag, ← map_inv]
  exact integralBound parameter realMatrix
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹

theorem finiteDimensional_summable_atInfinity {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (subspace : Submodule ℂ data.cusp.smooth) [FiniteDimensional ℂ subspace]
    (compactValues : ∀ realMatrix : RealGL3,
      realMatrix.val.transpose * realMatrix.val = 1 → ∀ integralMatrix : IntegralGL3,
      planeCuspVector (flatSection.1 cohomologicalPoint)
        (atInfinity realMatrix * atFinite (integralFinite integralMatrix)) ∈ subspace)
    (realMatrix : RealGL3) (parameter : ℂ)
    (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (eisensteinSummand sectionFamily parameter (atInfinity realMatrix)) := by
  obtain ⟨bound, _, scalarBound⟩ :=
    finiteDimensional_flag_real_comparison flatSection subspace compactValues
  exact ((TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicBounds.summable_norm_flag_cuspVectors_atInfinity
    flatSection realMatrix parameter rightHalfPlane).mul_left bound).of_norm_bounded
      (scalarBound parameter realMatrix)

theorem finiteDimensional_hasSum_atInfinity {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (subspace : Submodule ℂ data.cusp.smooth) [FiniteDimensional ℂ subspace]
    (compactValues : ∀ realMatrix : RealGL3,
      realMatrix.val.transpose * realMatrix.val = 1 → ∀ integralMatrix : IntegralGL3,
      planeCuspVector (flatSection.1 cohomologicalPoint)
        (atInfinity realMatrix * atFinite (integralFinite integralMatrix)) ∈ subspace)
    (realMatrix : RealGL3) (parameter : ℂ)
    (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter (atInfinity realMatrix))
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter (atInfinity realMatrix)) :=
  (finiteDimensional_summable_atInfinity flatSection subspace compactValues realMatrix parameter
    rightHalfPlane).hasSum

theorem finiteDimensional_analytic_atInfinity {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (subspace : Submodule ℂ data.cusp.smooth) [FiniteDimensional ℂ subspace]
    (compactValues : ∀ realMatrix : RealGL3,
      realMatrix.val.transpose * realMatrix.val = 1 → ∀ integralMatrix : IntegralGL3,
      planeCuspVector (flatSection.1 cohomologicalPoint)
        (atInfinity realMatrix * atFinite (integralFinite integralMatrix)) ∈ subspace)
    (realMatrix : RealGL3) :
    AnalyticOnNhd ℂ
      (fun parameter => TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter (atInfinity realMatrix))
      {parameter : ℂ | -(degree : ℝ) / 2 < parameter.re} := by
  intro parameter rightHalfPlane
  let reference : ℂ := (((-(degree : ℝ) / 2 + parameter.re) / 2 : ℝ) : ℂ)
  have referenceBound : -(degree : ℝ) / 2 < reference.re := by
    dsimp [reference]
    change -(degree : ℝ) / 2 < parameter.re at rightHalfPlane
    linarith
  have parameterBound : reference.re < parameter.re := by
    dsimp [reference]
    change -(degree : ℝ) / 2 < parameter.re at rightHalfPlane
    linarith
  exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.analytic_atInfinity_of_summable flatSection realMatrix reference
    (finiteDimensional_summable_atInfinity flatSection subspace compactValues realMatrix reference
      referenceBound) parameter parameterBound

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarFinite
