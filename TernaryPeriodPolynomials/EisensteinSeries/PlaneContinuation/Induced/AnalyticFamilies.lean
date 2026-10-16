module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.LocalAnalyticFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Realization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages TernaryPeriodPolynomials.PlaneEisensteinContinuation.LocalAnalyticFamilies
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedAnalyticFamilies

noncomputable def matrixCuspVector {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) (realMatrix : PlaneMatrix) : data.cusp.smooth :=
  planeCuspVector inducedSection (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding finiteMatrix) *
    atInfinity (invertibleMatrix realMatrix))

theorem matrixCuspVector_fixed {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) (realMatrix : PlaneMatrix) :
    (matrixCuspVector inducedSection finiteMatrix realMatrix).val ∈ fixedSubspace data.cusp finiteCongruence := by
  intro finiteElement
  obtain ⟨binaryMatrix, congruence, equality⟩ := finiteElement.property
  have fixed := cuspVector_integralCongruence_fixed inducedSection binaryMatrix congruence
    (invertibleMatrix realMatrix) finiteMatrix
  rw [equality, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute] at fixed
  exact fixed

theorem matrixCuspVector_joint_analyticAt {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) (realMatrix : RealGL3) :
    AnalyticAt ℝ (familyOrbit data.cusp (fun matrix => (matrixCuspVector inducedSection finiteMatrix matrix).val))
      (1, realMatrix.val) := by
  have membership : ((1 : BinaryMatrix), realMatrix.val) ∈ jointDomain :=
    ⟨by simp, Matrix.GeneralLinearGroup.det_ne_zero realMatrix⟩
  exact ((jointOrbit_contDiffOn inducedSection (Matrix.GeneralLinearGroup.map integralEmbedding finiteMatrix)
    (1, realMatrix.val) membership).contDiffAt (jointDomain_isOpen.mem_nhds membership)).analyticAt

theorem exists_cuspVector_localStageFamily {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) (realMatrix : RealGL3) :
    ∃ shiftRadius : ℝ≥0, 0 < shiftRadius ∧ ∃ coefficientRadius : ℝ≥0,
      ∃ positiveRadius : 0 < coefficientRadius,
      ∃ lift : ParameterBall shiftRadius → analyticStage data.cusp finiteCongruence coefficientRadius positiveRadius,
        Continuous lift ∧ ∀ offset,
          stageHilbertMap data.cusp finiteCongruence coefficientRadius positiveRadius (lift offset) =
            (matrixCuspVector inducedSection finiteMatrix (realMatrix.val + offset.val)).val := by
  obtain ⟨series, expansionRadius, expansion⟩ :=
    matrixCuspVector_joint_analyticAt inducedSection finiteMatrix realMatrix
  obtain ⟨radius, positiveRadius, radiusBound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp expansion.r_pos
  have radiusPositive : (0 : ℝ≥0) < radius := by exact_mod_cast positiveRadius
  have halfPositive : (0 : ℝ≥0) < radius / 2 := div_pos radiusPositive (by norm_num)
  have halfBound : ((radius / 2 : ℝ≥0) : ENNReal) + ((radius / 2 : ℝ≥0) : ENNReal) < expansionRadius := by
    rw [← ENNReal.coe_add, add_halves]
    exact radiusBound
  let family : PlaneMatrix → data.cusp.H := fun matrix => (matrixCuspVector inducedSection finiteMatrix matrix).val
  have fixed (offset : ParameterBall (radius / 2)) :
      family (realMatrix.val + offset.val) ∈ fixedSubspace data.cusp finiteCongruence :=
    matrixCuspVector_fixed inducedSection finiteMatrix _
  let lift := localStageFamily data.cusp finiteCongruence family realMatrix.val series expansionRadius expansion
    (radius / 2) (radius / 2) halfPositive halfBound fixed
  refine ⟨radius / 2, halfPositive, radius / 2, halfPositive, lift, ?_, ?_⟩
  · exact localStageFamily_continuous data.cusp finiteCongruence family realMatrix.val series expansionRadius expansion
      (radius / 2) (radius / 2) halfPositive halfBound fixed
  · intro offset
    exact stageHilbertMap_localStageFamily data.cusp finiteCongruence family realMatrix.val series expansionRadius expansion
      (radius / 2) (radius / 2) halfPositive halfBound fixed offset

theorem matrixCuspSupNorm_continuousAt_of_stage_continuity {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (stageContinuity : ∀ radius : ℝ≥0, ∀ positiveRadius : 0 < radius,
      Continuous (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticRealization.stageRealization data.cusp finiteCongruence
        finiteCongruence_isOpen finiteCongruence_isCompact radius positiveRadius))
    (finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) (realMatrix : RealGL3) :
    ContinuousAt (fun matrix : PlaneMatrix =>
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm (matrixCuspVector inducedSection finiteMatrix matrix)) realMatrix.val := by
  obtain ⟨shiftRadius, positiveShift, coefficientRadius, positiveRadius, lift, liftContinuous, liftValue⟩ :=
    exists_cuspVector_localStageFamily inducedSection finiteMatrix realMatrix
  have realizationContinuous := (stageContinuity coefficientRadius positiveRadius).comp liftContinuous
  have normContinuous := realizationContinuous.norm
  have equality : (fun offset : ParameterBall shiftRadius =>
      ‖TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticRealization.stageRealization data.cusp finiteCongruence finiteCongruence_isOpen
        finiteCongruence_isCompact coefficientRadius positiveRadius (lift offset)‖) =
      (fun offset => TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm
        (matrixCuspVector inducedSection finiteMatrix (realMatrix.val + offset.val))) := by
    funext offset
    change TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm (stageSmoothMap data.cusp finiteCongruence
      finiteCongruence_isOpen finiteCongruence_isCompact coefficientRadius positiveRadius (lift offset)).val = _
    apply congrArg TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm
    exact Subtype.ext (liftValue offset)
  exact continuousAt_of_parameterBall _ realMatrix.val shiftRadius positiveShift (equality ▸ normContinuous)

theorem realCuspSupNorm_continuous_of_stage_continuity {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (stageContinuity : ∀ radius : ℝ≥0, ∀ positiveRadius : 0 < radius,
      Continuous (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticRealization.stageRealization data.cusp finiteCongruence
        finiteCongruence_isOpen finiteCongruence_isCompact radius positiveRadius))
    (finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) :
    Continuous (fun realMatrix : RealGL3 =>
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm (matrixCuspVector inducedSection finiteMatrix realMatrix.val)) := by
  apply continuous_iff_continuousAt.mpr
  intro realMatrix
  exact (matrixCuspSupNorm_continuousAt_of_stage_continuity inducedSection stageContinuity finiteMatrix realMatrix).comp
    Units.continuous_val.continuousAt

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedAnalyticFamilies
