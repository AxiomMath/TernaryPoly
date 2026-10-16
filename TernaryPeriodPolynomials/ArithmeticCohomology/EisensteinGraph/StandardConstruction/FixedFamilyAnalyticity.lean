module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TranslatedCoefficientAnalyticity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RotationTypes
public import Mathlib.Analysis.Normed.Module.HahnBanach

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Filter Topology
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LocalAnalyticFamilies
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FixedFamilyAnalyticity


/-- Finite-mode admissibility transports joint Hilbert analyticity to the actual
scalar realization. The proof works in a fixed-radius Banach stage. -/
theorem scalar_analyticAt (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (finiteTypes : ∀ index : ℤ, FiniteDimensional ℂ (FiniteRotationTypes.fixedMode data level index))
    (family : PlaneMatrix → data.smooth)
    (fixed : ∀ matrix, (family matrix).val ∈ fixedSubspace data level)
    (center : PlaneMatrix)
    (joint : AnalyticAt ℝ (familyOrbit data (fun matrix => (family matrix).val)) (1, center))
    (test : BinaryAdelicGL) :
    AnalyticAt ℝ (fun matrix => data.realize (family matrix) test) center := by
  obtain ⟨series, expansionRadius, expansion⟩ := joint
  obtain ⟨radius, radiusPositive, radiusBound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp expansion.r_pos
  have positive : (0 : ℝ≥0) < radius := by exact_mod_cast radiusPositive
  have halfPositive : (0 : ℝ≥0) < radius / 2 := div_pos positive (by norm_num)
  have halfBound : ((radius / 2 : ℝ≥0) : ENNReal) + ((radius / 2 : ℝ≥0) : ENNReal) < expansionRadius := by
    rw [← ENNReal.coe_add, add_halves]
    exact radiusBound
  let coefficientRadius := radius / 2
  let coefficientPositive : 0 < coefficientRadius := halfPositive
  let stage := analyticStage data level coefficientRadius coefficientPositive
  let realization : stage →L[ℂ] lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
    ⟨AnalyticRealization.stageRealization data level openness compactness coefficientRadius coefficientPositive,
      FiniteRotationTypes.stageRealization_continuous_of_finite_types data level openness compactness
        finiteTypes coefficientRadius coefficientPositive⟩
  let evaluation : stage →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ test).comp realization
  obtain ⟨functional, extensionAgreement, _⟩ := exists_extension_norm_eq stage evaluation
  let restriction := CoefficientRestriction.restrictCoefficients (Target := data.H)
    (ContinuousLinearMap.inl ℝ BinaryMatrix PlaneMatrix)
    (ContinuousLinearMap.norm_inl_le_one ℝ BinaryMatrix PlaneMatrix)
  let ambient : PlaneMatrix → data.H × CoefficientSpace data := fun offset =>
    ((family (center + offset)).val,
      restriction (TranslatedCoefficientAnalyticity.value series coefficientRadius (0, offset)))
  have firstAnalytic : AnalyticAt ℝ (fun offset => (family (center + offset)).val) 0 := by
    have jointAnalytic : AnalyticAt ℝ (familyOrbit data (fun matrix => (family matrix).val)) (1, center) :=
      expansion.analyticAt
    have compose : AnalyticAt ℝ (fun offset : PlaneMatrix =>
        familyOrbit data (fun matrix => (family matrix).val) (1, center + offset)) 0 :=
      jointAnalytic.fun_comp_of_eq (analyticAt_const.prod (analyticAt_const.add analyticAt_id)) (by simp)
    simpa only [familyOrbit, AnalyticOrbit.realOrbit_one] using compose
  have secondAnalytic : AnalyticAt ℝ (fun offset : PlaneMatrix =>
      restriction (TranslatedCoefficientAnalyticity.value series coefficientRadius (0, offset))) 0 := by
    have analytic := TranslatedCoefficientAnalyticity.value_analyticAt_zero series
      coefficientRadius coefficientRadius halfPositive (halfBound.trans_le expansion.r_le)
    have inserted := analytic.fun_comp_of_eq (f := fun offset : PlaneMatrix => ((0 : BinaryMatrix), offset))
      (analyticAt_const.prod analyticAt_id) rfl
    exact (restriction.analyticAt _).fun_comp inserted
  have scalarAnalytic : AnalyticAt ℝ (fun offset => functional (ambient offset)) 0 :=
    ((functional.restrictScalars ℝ).analyticAt _).fun_comp (firstAnalytic.prod secondAnalytic)
  have shifted : AnalyticAt ℝ (fun offset => data.realize (family (center + offset)) test) 0 := by
    apply scalarAnalytic.congr
    have positiveReal : (0 : ℝ) < coefficientRadius := by exact_mod_cast coefficientPositive
    filter_upwards [Metric.closedBall_mem_nhds (0 : PlaneMatrix) positiveReal] with offset membership
    have offsetBound : ‖offset‖₊ ≤ coefficientRadius := by
      exact_mod_cast (show ‖offset‖ ≤ (coefficientRadius : ℝ) from by
        simpa only [Metric.mem_closedBall, dist_zero_right] using membership)
    let lift := localStageFamily data level (fun matrix => (family matrix).val) center series
      expansionRadius expansion coefficientRadius coefficientRadius coefficientPositive halfBound
      (fun shifted => fixed (center + shifted.val)) ⟨offset, offsetBound⟩
    have ambientEquality : ambient offset = lift.val := by
      apply Prod.ext
      · rfl
      · change restriction (TranslatedCoefficientAnalyticity.value series coefficientRadius (0, offset)) =
          restriction (TranslatedSeries.translatedCoefficients series coefficientRadius coefficientRadius
            (halfBound.trans_le expansion.r_le) (jointShift coefficientRadius ⟨offset, offsetBound⟩))
        exact congrArg restriction (TranslatedCoefficientAnalyticity.value_eq_translatedCoefficients series
          coefficientRadius coefficientRadius (halfBound.trans_le expansion.r_le)
          (jointShift coefficientRadius ⟨offset, offsetBound⟩))
    rw [ambientEquality, extensionAgreement lift]
    change data.realize (stageSmoothMap data level openness compactness coefficientRadius coefficientPositive lift).val test = _
    congr 1
  have original := shifted.fun_comp_of_eq (f := fun matrix : PlaneMatrix => matrix - center)
    (analyticAt_id.sub analyticAt_const) (sub_self center)
  simpa only [add_sub_cancel] using original

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FixedFamilyAnalyticity
