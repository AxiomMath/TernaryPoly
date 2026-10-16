module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.StageLift
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.ProfileCutoff

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealProfileRegularity TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedAnalyticFamilies
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealProfileStage

theorem exists_local_lift {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function)
    (finitePoint : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ∃ domain : Set (Rectangular ℝ), IsOpen domain ∧ frame ∈ domain ∧
      domain ⊆ {value : Rectangular ℝ | FullRank value} ∧
      ∃ radius : ℝ≥0, ∃ positiveRadius : 0 < radius,
      ∃ lift : Rectangular ℝ → analyticStage data.cusp finiteCongruence radius positiveRadius,
        AnalyticOnNhd ℝ lift domain ∧ ∀ value ∈ domain,
          stageHilbertMap data.cusp finiteCongruence radius positiveRadius (lift value) =
            (profile induced (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding finitePoint) value)).val := by
  let realMatrix := invertibleMatrix (inverseMatrix frame)
  have matrixValue : realMatrix.val = inverseMatrix frame :=
    invertibleMatrix_val _ (inverseMatrix_det_ne_zero frame fullRank)
  obtain ⟨shiftRadius, positiveShift, radius, positiveRadius, matrixLift, analyticLift, liftValue⟩ :=
    InducedStageLift.exists_analytic_lift induced finitePoint realMatrix
  let offset : Rectangular ℝ → PlaneMatrix := fun value => inverseMatrix value - realMatrix.val
  let domain : Set (Rectangular ℝ) := {value | FullRank value} ∩ offset ⁻¹' Metric.eball 0 (shiftRadius : ENNReal)
  have offsetSmooth (value : Rectangular ℝ) (rank : FullRank value) : ContDiffAt ℝ ⊤ offset value :=
    (inverseMatrix_contDiffAt value rank).sub contDiffAt_const
  have openDomain : IsOpen domain := by
    apply isOpen_iff_mem_nhds.mpr
    intro value membership
    exact Filter.inter_mem (fullRank_isOpen.mem_nhds membership.1)
      ((offsetSmooth value membership.1).continuousAt.preimage_mem_nhds (Metric.isOpen_eball.mem_nhds membership.2))
  have centerMembership : frame ∈ domain := by
    refine ⟨fullRank, ?_⟩
    have zeroOffset : offset frame = 0 := by dsimp [offset]; rw [matrixValue, sub_self]
    rw [Set.mem_preimage, zeroOffset, Metric.mem_eball, edist_self]
    exact_mod_cast positiveShift
  let finiteMatrix := Matrix.GeneralLinearGroup.map integralEmbedding finitePoint
  let lift : Rectangular ℝ → analyticStage data.cusp finiteCongruence radius positiveRadius :=
    fun value => coefficient data parameter finiteMatrix value • matrixLift (offset value)
  refine ⟨domain, openDomain, centerMembership, (fun _ membership => membership.1), radius, positiveRadius, lift, ?_, ?_⟩
  · intro value membership
    have scalarAnalytic : AnalyticAt ℝ (coefficient data parameter finiteMatrix) value :=
      ((coefficient_contDiffOn data parameter finiteMatrix).contDiffAt
        (fullRank_isOpen.mem_nhds membership.1)).analyticAt
    have vectorAnalytic := (analyticLift (offset value) membership.2).comp (offsetSmooth value membership.1).analyticAt
    exact scalarAnalytic.smul vectorAnalytic
  · intro value membership
    change stageHilbertMap data.cusp finiteCongruence radius positiveRadius
      (coefficient data parameter finiteMatrix value • matrixLift (offset value)) = _
    rw [map_smul, liftValue (offset value) membership.2,
      profile_eq_model induced finiteMatrix value membership.1]
    have offsetCancel : realMatrix.val + offset value = inverseMatrix value := by
      dsimp [offset]
      abel
    rw [offsetCancel]
    rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealProfileStage
