module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.CuspRegularity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.StageLift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedAnalyticFamilies TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open scoped Classical Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BoundedSmoothRealization

def evaluation {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]
    {degree : ℕ} (data : InducingData degree) (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun source => (family source).val.val)) (point : BinaryAdelicGL) : Source →L[ℂ] ℂ :=
  ⟨(LinearMap.proj point).comp (data.cusp.realize.comp ((fixedSmooth data.cusp finiteCongruence).subtype.comp family)),
    (lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ point).continuous.comp
      (FiniteRotationTypes.realization_continuous_of_finite_types data.cusp finiteCongruence
        finiteCongruence_isOpen finiteCongruence_isCompact (EndpointAdmissibility.all_finiteDimensional data) family continuous)⟩

theorem matrixCuspVector_analyticAt {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (linear : data.cusp.smooth →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (bounded : data.cusp.H →L[ℂ] data.cusp.H)
    (compatibility : ∀ vector : data.cusp.smooth, (linear vector).val.val = bounded vector.val)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (evaluationPoint : BinaryAdelicGL) :
    AnalyticAt ℝ (fun matrix : PlaneMatrix => data.cusp.realize (linear (matrixCuspVector induced point matrix)).val evaluationPoint)
      realPoint.val := by
  obtain ⟨shiftRadius, positiveShift, coefficientRadius, positiveRadius, lift, analytic, image⟩ :=
    InducedStageLift.exists_analytic_lift induced point realPoint
  let family : analyticStage data.cusp finiteCongruence coefficientRadius positiveRadius →ₗ[ℂ]
      fixedSmooth data.cusp finiteCongruence := linear.comp
    ((fixedSmooth data.cusp finiteCongruence).subtype.comp
      (stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact coefficientRadius positiveRadius))
  have continuous : Continuous (fun source => (family source).val.val) := by
    change Continuous (fun source => (linear ((stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen
      finiteCongruence_isCompact coefficientRadius positiveRadius source).val)).val.val)
    simp only [compatibility]
    exact bounded.continuous.comp (stageHilbertMap data.cusp finiteCongruence coefficientRadius positiveRadius).continuous
  let functional := evaluation data family continuous evaluationPoint
  have zeroMem : (0 : PlaneMatrix) ∈ Metric.eball 0 (shiftRadius : ENNReal) := by
    simpa only [Metric.mem_eball, edist_self] using (show (0 : ENNReal) < (shiftRadius : ENNReal) by exact_mod_cast positiveShift)
  have liftAt : AnalyticAt ℝ lift (realPoint.val - realPoint.val) := by
    simpa only [sub_self] using analytic 0 zeroMem
  have offsetAt : AnalyticAt ℝ (fun matrix : PlaneMatrix => matrix - realPoint.val) realPoint.val :=
    analyticAt_id.sub analyticAt_const
  have composite : AnalyticAt ℝ (fun matrix : PlaneMatrix => functional (lift (matrix - realPoint.val))) realPoint.val :=
    ((functional.restrictScalars ℝ).analyticAt _).comp
      (liftAt.comp (f := fun matrix : PlaneMatrix => matrix - realPoint.val) offsetAt)
  have nearby : ∀ᶠ matrix : PlaneMatrix in nhds realPoint.val,
      matrix - realPoint.val ∈ Metric.eball 0 (shiftRadius : ENNReal) :=
    offsetAt.continuousAt.tendsto.eventually (by
      change Metric.eball (0 : PlaneMatrix) (shiftRadius : ENNReal) ∈ nhds (realPoint.val - realPoint.val)
      rw [sub_self]
      exact Metric.isOpen_eball.mem_nhds zeroMem)
  apply composite.congr
  filter_upwards [nearby] with matrix membership
  have vectorEquality :
      (stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
        coefficientRadius positiveRadius (lift (matrix - realPoint.val))).val = matrixCuspVector induced point matrix := by
    apply Subtype.ext
    have equality := image (matrix - realPoint.val) membership
    rw [add_sub_cancel] at equality
    exact equality
  change data.cusp.realize (linear ((stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
    coefficientRadius positiveRadius (lift (matrix - realPoint.val))).val)).val evaluationPoint = _
  rw [vectorEquality]

theorem smooth_of_analytic (function : RealGL3 → ℂ)
    (analytic : ∀ realPoint : RealGL3,
      AnalyticAt ℝ (fun matrix : PlaneMatrix => function (invertibleMatrix matrix)) realPoint.val)
    (realPoint : RealGL3) : Smooth (fun matrices : Fin 1 → RealGL3 => function (realPoint * matrices 0)) := by
  have smooth : ContDiffOn ℝ ⊤ (fun matrix : PlaneMatrix => function (invertibleMatrix matrix))
      {matrix : PlaneMatrix | matrix.det ≠ 0} := by
    intro matrix invertible
    have result := (analytic (invertibleMatrix matrix)).contDiffAt (n := (⊤ : WithTop ℕ∞))
    rw [OrbitSmooth.invertibleMatrix_val matrix invertible] at result
    exact result.contDiffWithinAt
  have multiplication : ContDiff ℝ ⊤ (fun matrices : Fin 1 → PlaneMatrix => realPoint.val * matrices 0) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    simp only [Matrix.mul_apply]
    apply ContDiff.sum
    intro index _
    fun_prop
  have membership : Set.MapsTo (fun matrices : Fin 1 → PlaneMatrix => realPoint.val * matrices 0)
      {matrices | ∀ i, (matrices i).det ≠ 0} {matrix | matrix.det ≠ 0} := by
    intro matrices invertible
    simp only [Set.mem_ofPred_eq, Matrix.det_mul]
    exact mul_ne_zero (GeneralLinearGroup.det_ne_zero realPoint) (invertible 0)
  apply (smooth.comp multiplication.contDiffOn membership).congr
  intro matrices invertible
  change function (realPoint * invertibleMatrix (matrices 0)) = function (invertibleMatrix (realPoint.val * matrices 0))
  apply congrArg function
  apply Units.ext
  rw [Units.val_mul, OrbitSmooth.invertibleMatrix_val (matrices 0) (invertible 0),
    OrbitSmooth.invertibleMatrix_val _ (membership invertible)]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BoundedSmoothRealization
