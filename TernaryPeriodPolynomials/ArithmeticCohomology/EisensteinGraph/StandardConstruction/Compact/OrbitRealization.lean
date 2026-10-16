module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarRealization
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LocalAnalyticFamilies
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactOrbitRealization

instance parameterBallMeasurableSpace (radius : ℝ≥0) :
    MeasurableSpace (ParameterBall radius) := borel _

instance parameterBallBorelSpace (radius : ℝ≥0) : BorelSpace (ParameterBall radius) := ⟨rfl⟩

def stageRealizationCLM {degree : ℕ} (data : InducingData degree)
    (radius : ℝ≥0) (positive : 0 < radius) :
    analyticStage data.cusp finiteCongruence radius positive →L[ℂ]
      lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
  ⟨AnalyticRealization.stageRealization data.cusp finiteCongruence
    finiteCongruence_isOpen finiteCongruence_isCompact radius positive,
   FiniteRotationTypes.continuousStages_of_finite_types data.cusp
    (EndpointAdmissibility.all_finiteDimensional data) radius positive⟩

theorem stage_integral {degree : ℕ} (data : InducingData degree)
    (radius : ℝ≥0) (positive : 0 < radius)
    {Parameter : Type} [MeasurableSpace Parameter] (measure : Measure Parameter)
    (family : Parameter → analyticStage data.cusp finiteCongruence radius positive)
    (integrable : Integrable family measure) :
    ∃ vector : data.cusp.smooth,
      vector.val = ∫ parameter, stageHilbertMap data.cusp finiteCongruence radius positive
        (family parameter) ∂measure ∧
      ∀ binary, data.cusp.realize vector binary =
        ∫ parameter, stageRealizationCLM data radius positive (family parameter) binary
          ∂measure := by
  let vector := (stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen
    finiteCongruence_isCompact radius positive (∫ parameter, family parameter ∂measure)).val
  refine ⟨vector, ?_, ?_⟩
  · exact ((stageHilbertMap data.cusp finiteCongruence radius positive).integral_comp_comm
      integrable).symm
  · intro binary
    let evaluation := (lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ binary).comp
      (stageRealizationCLM data radius positive)
    exact (evaluation.integral_comp_comm integrable).symm

theorem matrix_realization_continuousAt {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (finite : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) (real : RealGL3) :
    ContinuousAt (fun matrix : PlaneMatrix => CuspSupNorm.boundedRealization data.cusp
      (InducedAnalyticFamilies.matrixCuspVector induced finite matrix)) real.val := by
  obtain ⟨shiftRadius, positiveShift, radius, positive, lift, continuousLift, liftValue⟩ :=
    InducedAnalyticFamilies.exists_cuspVector_localStageFamily induced finite real
  apply continuousAt_of_parameterBall _ real.val shiftRadius positiveShift
  have equality : (fun offset : ParameterBall shiftRadius =>
      CuspSupNorm.boundedRealization data.cusp
        (InducedAnalyticFamilies.matrixCuspVector induced finite (real.val + offset.val))) =
      fun offset => stageRealizationCLM data radius positive (lift offset) := by
    funext offset
    change CuspSupNorm.boundedRealization data.cusp _ =
      CuspSupNorm.boundedRealization data.cusp
        (stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen
          finiteCongruence_isCompact radius positive (lift offset)).val
    congr 1
    exact Subtype.ext (liftValue offset).symm
  rw [equality]
  exact (stageRealizationCLM data radius positive).continuous.comp continuousLift

theorem real_realization_continuous {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (finite : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) :
    Continuous (fun real : RealGL3 => CuspSupNorm.boundedRealization data.cusp
      (CuspLift.vector data .plane parameter function induced
        (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding finite) *
          atInfinity real))) := by
  apply continuous_iff_continuousAt.mpr
  intro real
  have continuity := (matrix_realization_continuousAt data parameter function induced
    finite real).comp Units.continuous_val.continuousAt
  convert continuity using 1
  funext value
  rw [CompactScalarRealization.cuspLift_eq_reference]
  simp only [Function.comp_apply, InducedAnalyticFamilies.matrixCuspVector,
    invertibleMatrix_units]

theorem parameterBall_compact (radius : ℝ≥0) :
    IsCompact {offset : PlaneMatrix | ‖offset‖₊ ≤ radius} := by
  have equality : {offset : PlaneMatrix | ‖offset‖₊ ≤ radius} =
      Metric.closedBall 0 (radius : ℝ) := by
    ext offset
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    exact NNReal.coe_le_coe.symm
  rw [equality]
  exact isCompact_closedBall _ _

/-- Every sufficiently small compact real orbit has an actual smooth Hilbert
integral, and its automorphic realization is the integral at every binary adele. -/
theorem exists_local_integral_realization {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (finite : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) (real : RealGL3) :
    ∃ radius : ℝ≥0, 0 < radius ∧
      ∀ (measure : Measure (ParameterBall radius)), IsFiniteMeasure measure →
        ∃ vector : data.cusp.smooth,
          vector.val = ∫ offset, (InducedAnalyticFamilies.matrixCuspVector induced finite
            (real.val + offset.val)).val ∂measure ∧
          ∀ binary, data.cusp.realize vector binary =
            ∫ offset, data.cusp.realize (InducedAnalyticFamilies.matrixCuspVector
              induced finite (real.val + offset.val)) binary ∂measure := by
  obtain ⟨shiftRadius, positiveShift, radius, positive, lift, continuousLift, liftValue⟩ :=
    InducedAnalyticFamilies.exists_cuspVector_localStageFamily induced finite real
  refine ⟨shiftRadius, positiveShift, ?_⟩
  intro measure finiteMeasure
  let _ : IsFiniteMeasure measure := finiteMeasure
  let _ : CompactSpace (ParameterBall shiftRadius) :=
    isCompact_iff_compactSpace.mp (parameterBall_compact shiftRadius)
  have integrable : Integrable lift measure := by
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact (μ := measure) isCompact_univ
        continuousLift.continuousOn)
  obtain ⟨vector, hilbert, scalar⟩ := stage_integral data radius positive measure lift integrable
  refine ⟨vector, ?_, ?_⟩
  · simpa only [liftValue] using hilbert
  · intro binary
    rw [scalar binary]
    apply integral_congr_ae
    filter_upwards [] with offset
    change data.cusp.realize
      (stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen
        finiteCongruence_isCompact radius positive (lift offset)).val binary = _
    have vectorEquality :
        (stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen
          finiteCongruence_isCompact radius positive (lift offset)).val =
        InducedAnalyticFamilies.matrixCuspVector induced finite (real.val + offset.val) :=
      Subtype.ext (liftValue offset)
    rw [vectorEquality]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactOrbitRealization
