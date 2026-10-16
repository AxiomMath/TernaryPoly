module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.GlobalSeries
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.Finite
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Smooth.Bounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalScalar

theorem height_bound_of_compact_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (bound : ℝ)
    (compactBound : ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      cuspSupNorm (planeCuspVector (flatSection.1 cohomologicalPoint) compactElement) ≤ bound)
    (parameter : ℂ) (matrix : AdelicGL) :
    ‖sectionFamily parameter matrix‖ ≤
      Real.exp (((degree : ℝ) + 3) / 3 * Real.log (adeleNorm (Matrix.GeneralLinearGroup.det matrix) : ℝ) +
        (parameter.re + ((degree : ℝ) + 6) / 2) * height matrix) * bound := by
  have formula := TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarFinite.cuspSupNorm_planeParabolic (flatSection.1 parameter)
    (parabolicPart matrix) (compactPart matrix)
  rw [← parabolicPart_mul_compactPart, TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalBounds.parabolic_exponent_eq] at formula
  rw [induced_eq_planeCuspVector_one (flatSection.1 parameter)]
  apply (realize_le_cuspSupNorm _ 1).trans
  rw [formula, flatSection_planeCuspVector_eq flatSection parameter _ (compactPart_mem matrix)]
  exact mul_le_mul_of_nonneg_left (compactBound _ (compactPart_mem matrix)) (Real.exp_pos _).le

theorem summable_of_compact_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (bound : ℝ) (nonnegativeBound : 0 ≤ bound)
    (compactBound : ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      cuspSupNorm (planeCuspVector (flatSection.1 cohomologicalPoint) compactElement) ≤ bound)
    (basePoint : AdelicGL) (parameter : ℂ)
    (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (eisensteinSummand sectionFamily parameter basePoint) := by
  apply Summable.of_norm
  apply TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalBounds.summable_norm_of_height_bound basePoint _
    (parameter.re + ((degree : ℝ) + 6) / 2)
    (((degree : ℝ) + 3) / 3 * Real.log (adeleNorm (Matrix.GeneralLinearGroup.det basePoint) : ℝ))
    bound (by linarith) nonnegativeBound
  intro flag
  have boundProperty := height_bound_of_compact_bound flatSection bound compactBound parameter
    (rationalGroup flag.out⁻¹ * basePoint)
  rwa [TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalBounds.adeleNorm_det_rational_mul] at boundProperty

theorem hasSum_of_compact_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (bound : ℝ) (nonnegativeBound : 0 ≤ bound)
    (compactBound : ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      cuspSupNorm (planeCuspVector (flatSection.1 cohomologicalPoint) compactElement) ≤ bound)
    (basePoint : AdelicGL) (parameter : ℂ)
    (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter basePoint)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter basePoint) :=
  (summable_of_compact_bound flatSection bound nonnegativeBound compactBound basePoint parameter
    rightHalfPlane).hasSum

theorem finiteDimensional_comparison {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (subspace : Submodule ℂ data.cusp.smooth) [FiniteDimensional ℂ subspace]
    (compactValues : ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      planeCuspVector (flatSection.1 cohomologicalPoint) compactElement ∈ subspace) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ matrix : AdelicGL,
      ‖sectionFamily parameter matrix‖ ≤
        bound * ‖(planeCuspVector (flatSection.1 parameter) matrix).val‖ := by
  obtain ⟨bound, nonnegativeBound, subspaceBound⟩ := finiteDimensional_cuspSupNorm_bound subspace
  refine ⟨bound, nonnegativeBound, fun parameter matrix => ?_⟩
  have compactComparison : cuspSupNorm (planeCuspVector (flatSection.1 parameter) (compactPart matrix)) ≤
      bound * ‖(planeCuspVector (flatSection.1 parameter) (compactPart matrix)).val‖ := by
    rw [flatSection_planeCuspVector_eq flatSection parameter _ (compactPart_mem matrix)]
    exact subspaceBound _ (compactValues _ (compactPart_mem matrix))
  have comparison := TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarFinite.cuspSupNorm_comparison_planeParabolic (flatSection.1 parameter)
    (parabolicPart matrix) (compactPart matrix) bound compactComparison
  rw [← parabolicPart_mul_compactPart] at comparison
  rw [induced_eq_planeCuspVector_one (flatSection.1 parameter)]
  exact (realize_le_cuspSupNorm _ 1).trans comparison

theorem finiteDimensional_summable {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (subspace : Submodule ℂ data.cusp.smooth) [FiniteDimensional ℂ subspace]
    (compactValues : ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      planeCuspVector (flatSection.1 cohomologicalPoint) compactElement ∈ subspace)
    (basePoint : AdelicGL) (parameter : ℂ)
    (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (eisensteinSummand sectionFamily parameter basePoint) := by
  obtain ⟨bound, _, boundProperty⟩ := finiteDimensional_comparison flatSection subspace compactValues
  exact ((TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalBounds.summable_norm_flag_cuspVectors flatSection basePoint parameter
    rightHalfPlane).mul_left bound).of_norm_bounded (fun flag => boundProperty parameter _)

theorem finiteDimensional_hasSum {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (subspace : Submodule ℂ data.cusp.smooth) [FiniteDimensional ℂ subspace]
    (compactValues : ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      planeCuspVector (flatSection.1 cohomologicalPoint) compactElement ∈ subspace)
    (basePoint : AdelicGL) (parameter : ℂ)
    (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter basePoint)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter basePoint) :=
  (finiteDimensional_summable flatSection subspace compactValues basePoint parameter rightHalfPlane).hasSum

theorem finiteDimensional_analytic {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (subspace : Submodule ℂ data.cusp.smooth) [FiniteDimensional ℂ subspace]
    (compactValues : ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      planeCuspVector (flatSection.1 cohomologicalPoint) compactElement ∈ subspace)
    (basePoint : AdelicGL) :
    AnalyticOnNhd ℂ (fun parameter => TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter basePoint)
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
  exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalSeries.analytic_of_summable flatSection basePoint reference
    (finiteDimensional_summable flatSection subspace compactValues basePoint reference referenceBound)
    parameter parameterBound

theorem compact_bound_of_derivative_estimate {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (order : ℕ)
    (constant : ℝ) (nonnegativeConstant : 0 ≤ constant)
    (derivativeEstimate : ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      cuspSupNorm (planeCuspVector (flatSection.1 cohomologicalPoint) compactElement) ≤
        constant * TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds.compactDerivativeSum
          (flatSection.1 cohomologicalPoint) order compactElement) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      cuspSupNorm (planeCuspVector (flatSection.1 cohomologicalPoint) compactElement) ≤ bound := by
  obtain ⟨bound, nonnegativeBound, boundProperty⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds.compactDerivativeSum_bound (flatSection.1 cohomologicalPoint) order
  exact ⟨constant * bound, mul_nonneg nonnegativeConstant nonnegativeBound,
    fun compactElement compactness => (derivativeEstimate compactElement compactness).trans
      (mul_le_mul_of_nonneg_left (boundProperty compactElement compactness) nonnegativeConstant)⟩

theorem hasSum_of_derivative_estimate {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (order : ℕ)
    (constant : ℝ) (nonnegativeConstant : 0 ≤ constant)
    (derivativeEstimate : ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      cuspSupNorm (planeCuspVector (flatSection.1 cohomologicalPoint) compactElement) ≤
        constant * TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds.compactDerivativeSum
          (flatSection.1 cohomologicalPoint) order compactElement)
    (basePoint : AdelicGL) (parameter : ℂ)
    (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter basePoint)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter basePoint) := by
  obtain ⟨bound, nonnegativeBound, boundProperty⟩ := compact_bound_of_derivative_estimate
    flatSection order constant nonnegativeConstant derivativeEstimate
  exact hasSum_of_compact_bound flatSection bound nonnegativeBound boundProperty basePoint parameter
    rightHalfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalScalar
