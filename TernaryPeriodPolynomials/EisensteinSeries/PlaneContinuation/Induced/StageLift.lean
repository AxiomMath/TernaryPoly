module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.AnalyticFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.StageFamilies

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages TernaryPeriodPolynomials.PlaneEisensteinContinuation.LocalAnalyticFamilies
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedAnalyticFamilies TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedStageLift

theorem exists_analytic_lift {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) (realMatrix : RealGL3) :
    ∃ shiftRadius : ℝ≥0, 0 < shiftRadius ∧ ∃ coefficientRadius : ℝ≥0,
      ∃ positiveRadius : 0 < coefficientRadius,
      ∃ lift : PlaneMatrix → analyticStage data.cusp finiteCongruence coefficientRadius positiveRadius,
        AnalyticOnNhd ℝ lift (Metric.eball 0 (shiftRadius : ENNReal)) ∧
        ∀ offset ∈ Metric.eball 0 (shiftRadius : ENNReal),
          stageHilbertMap data.cusp finiteCongruence coefficientRadius positiveRadius (lift offset) =
            (matrixCuspVector induced finiteMatrix (realMatrix.val + offset)).val := by
  obtain ⟨series, expansionRadius, expansion⟩ := matrixCuspVector_joint_analyticAt induced finiteMatrix realMatrix
  obtain ⟨radius, positiveRadius, radiusBound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp expansion.r_pos
  have radiusPositive : (0 : ℝ≥0) < radius := by exact_mod_cast positiveRadius
  have halfPositive : (0 : ℝ≥0) < radius / 2 := div_pos radiusPositive (by norm_num)
  have halfBound : ((radius / 2 : ℝ≥0) : ENNReal) + ((radius / 2 : ℝ≥0) : ENNReal) < expansionRadius := by
    rw [← ENNReal.coe_add, add_halves]
    exact radiusBound
  let family : PlaneMatrix → data.cusp.H := fun matrix => (matrixCuspVector induced finiteMatrix matrix).val
  have fixed (offset : ParameterBall (radius / 2)) :
      family (realMatrix.val + offset.val) ∈ fixedSubspace data.cusp finiteCongruence :=
    matrixCuspVector_fixed induced finiteMatrix _
  let lift := AnalyticStageFamilies.stageFamily data.cusp finiteCongruence family realMatrix.val series expansionRadius expansion
    (radius / 2) (radius / 2) halfPositive halfBound fixed
  refine ⟨radius / 2, halfPositive, radius / 2, halfPositive, lift, ?_, ?_⟩
  · exact AnalyticStageFamilies.stageFamily_analyticOnNhd data.cusp finiteCongruence family realMatrix.val
      series expansionRadius expansion (radius / 2) (radius / 2) halfPositive halfPositive halfBound fixed
  · intro offset membership
    have bound : ‖offset‖₊ ≤ radius / 2 := by
      have strict : ‖offset‖₊ < radius / 2 := by
        simpa only [Metric.mem_eball, edist_lt_coe, nndist_zero_right] using membership
      exact strict.le
    exact congrArg Prod.fst (AnalyticStageFamilies.stageFamily_val data.cusp finiteCongruence family realMatrix.val
      series expansionRadius expansion (radius / 2) (radius / 2) halfPositive halfBound fixed offset bound)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedStageLift
