module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Height
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.Bounds

theorem norm_planeCuspVector_planeParabolic {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (parabolicElement : planeParabolic Adeles) (basePoint : AdelicGL) :
    ‖(planeCuspVector inducedSection (parabolicElement.val * basePoint)).val‖ =
      Real.exp ((-2 * inductionExponent .plane parameter).re *
          Real.log (adeleNorm (planeCornerUnit parabolicElement) : ℝ) +
        (binaryInductionExponent degree .plane parameter).re *
          Real.log (adeleNorm
            (Matrix.GeneralLinearGroup.det (planeBinaryBlock parabolicElement)) : ℝ)) *
        ‖(planeCuspVector inducedSection basePoint).val‖ := by
  rw [planeCuspVector_planeParabolic]
  change ‖(data.chi.toMonoidHom (planeCornerUnit parabolicElement) *
      normPower (planeCornerUnit parabolicElement) (-2 * inductionExponent .plane parameter)) •
    (normPower (Matrix.GeneralLinearGroup.det (planeBinaryBlock parabolicElement))
      (binaryInductionExponent degree .plane parameter) •
      data.cusp.π (planeBinaryBlock parabolicElement)
        (planeCuspVector inducedSection basePoint).val)‖ = _
  rw [norm_smul, norm_smul, norm_mul, data.chi.unitary, one_mul,
    data.cusp.unitary, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.norm_normPower,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.norm_normPower, Real.exp_add, mul_assoc]

theorem norm_planeCuspVector_real {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (realMatrix : RealGL3) (parabolicElement : planeParabolic ℝ)
    (orthogonalElement : RealGL3)
    (factorization : realMatrix = parabolicElement.val * orthogonalElement)
    (orthogonality : orthogonalElement.val.transpose * orthogonalElement.val = 1)
    (cornerValue : (planeCornerUnit parabolicElement).val =
      ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
        EuclideanSpace ℝ (Fin 3))‖) :
    ‖(planeCuspVector inducedSection (atInfinity realMatrix)).val‖ =
      Real.exp ((((degree : ℝ) + 4) / 2 + parameter.re / 3) *
          Real.log |realMatrix.val.det| -
        (parameter.re + ((degree : ℝ) + 6) / 2) *
          Real.log ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
            EuclideanSpace ℝ (Fin 3))‖) *
        ‖(planeCuspVector inducedSection (atInfinity orthogonalElement)).val‖ := by
  have embeddedFactorization : atInfinity realMatrix =
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.planeParabolicAtInfinity parabolicElement).val *
        atInfinity orthogonalElement := by
    rw [factorization, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
    rfl
  rw [embeddedFactorization, norm_planeCuspVector_planeParabolic,
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

theorem flatSection_real_cuspVector_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ realMatrix : RealGL3,
      ‖(planeCuspVector (flatSection.1 parameter) (atInfinity realMatrix)).val‖ ≤
        Real.exp ((((degree : ℝ) + 4) / 2 + parameter.re / 3) *
            Real.log |realMatrix.val.det| -
          (parameter.re + ((degree : ℝ) + 6) / 2) *
            Real.log ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
              EuclideanSpace ℝ (Fin 3))‖) * bound := by
  obtain ⟨bound, nonnegativeBound, compactBound⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Compact.planeCuspVector_bound_on_orthogonal
      (flatSection.1 cohomologicalPoint) 1
  refine ⟨bound, nonnegativeBound, fun parameter realMatrix => ?_⟩
  obtain ⟨parabolicElement, orthogonalElement, factorization, orthogonality, cornerValue⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.exists_plane_orthogonal realMatrix
  rw [norm_planeCuspVector_real (flatSection.1 parameter) realMatrix parabolicElement
    orthogonalElement factorization orthogonality cornerValue,
    flatSection_planeCuspVector_eq flatSection parameter (atInfinity orthogonalElement)
      ((TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.inMaximalCompact_atInfinity orthogonalElement).mpr orthogonality)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simpa only [one_mul] using compactBound orthogonalElement orthogonality

theorem lastRow_norm_pos (realMatrix : RealGL3) :
    0 < ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
      EuclideanSpace ℝ (Fin 3))‖ := by
  apply norm_pos_iff.mpr
  intro zeroRow
  exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.lastRow_ne_zero realMatrix
    (congrArg WithLp.ofLp zeroRow)

theorem flatSection_real_cuspVector_rpow_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ realMatrix : RealGL3,
      ‖(planeCuspVector (flatSection.1 parameter) (atInfinity realMatrix)).val‖ ≤
        |realMatrix.val.det| ^ (((degree : ℝ) + 4) / 2 + parameter.re / 3) *
          ‖(WithLp.toLp 2 (fun column : Fin 3 => realMatrix.val 2 column) :
            EuclideanSpace ℝ (Fin 3))‖ ^ (-(parameter.re + ((degree : ℝ) + 6) / 2)) *
          bound := by
  obtain ⟨bound, nonnegativeBound, matrixBound⟩ := flatSection_real_cuspVector_bound flatSection
  refine ⟨bound, nonnegativeBound, fun parameter realMatrix => ?_⟩
  rw [Real.rpow_def_of_pos (abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero realMatrix)),
    Real.rpow_def_of_pos (lastRow_norm_pos realMatrix), ← Real.exp_add]
  convert matrixBound parameter realMatrix using 1
  congr 2
  ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.Bounds
