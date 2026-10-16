module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.LocalAnalyticFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.TranslatedAnalytic
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ClosedSubspaceAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LocalAnalyticFamilies TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientRestriction
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStageFamilies

def coefficients (data : CuspidalRepresentation)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : PlaneMatrix) : CoefficientSpace data :=
  restrictCoefficients (ContinuousLinearMap.inl ℝ BinaryMatrix PlaneMatrix)
    (ContinuousLinearMap.norm_inl_le_one ℝ BinaryMatrix PlaneMatrix)
    (TranslatedAnalytic.family series shiftRadius coefficientRadius radiusBound (0, offset))

theorem coefficients_eq (data : CuspidalRepresentation)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : PlaneMatrix) (membership : ‖offset‖₊ ≤ shiftRadius) :
    coefficients data series shiftRadius coefficientRadius radiusBound offset =
      localCoefficients data series shiftRadius coefficientRadius radiusBound ⟨offset, membership⟩ := by
  have jointMembership : ‖((0 : BinaryMatrix), offset)‖₊ ≤ shiftRadius := by
    simpa only [Prod.nnnorm_mk, nnnorm_zero, zero_le, max_eq_right] using membership
  simp only [coefficients, TranslatedAnalytic.family, dite_eq_left jointMembership, localCoefficients, jointShift]
  rfl

theorem coefficients_analyticOnNhd (data : CuspidalRepresentation)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (shiftRadius coefficientRadius : ℝ≥0)
    (positiveShift : 0 < shiftRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius) :
    AnalyticOnNhd ℝ (coefficients data series shiftRadius coefficientRadius radiusBound)
      (Metric.eball 0 (shiftRadius : ENNReal)) := by
  intro offset membership
  have jointMembership : ((0 : BinaryMatrix), offset) ∈ Metric.eball 0 (shiftRadius : ENNReal) := by
    simpa only [Metric.mem_eball, edist_nndist, nndist_zero_right, Prod.nnnorm_mk,
      nnnorm_zero, zero_le, max_eq_right] using membership
  have analytic := (TranslatedAnalytic.family_analyticOnNhd series shiftRadius coefficientRadius positiveShift radiusBound)
    (0, offset) jointMembership
  have inserted := analytic.comp ((ContinuousLinearMap.inr ℝ BinaryMatrix PlaneMatrix).analyticAt offset)
  exact (((restrictCoefficients (Target := data.H) (ContinuousLinearMap.inl ℝ BinaryMatrix PlaneMatrix)
    (ContinuousLinearMap.norm_inl_le_one ℝ BinaryMatrix PlaneMatrix)).restrictScalars ℝ).analyticAt _).comp inserted

def stageFamily (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (family : PlaneMatrix → data.H) (center : PlaneMatrix)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (familyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < expansionRadius)
    (fixed : ∀ offset : ParameterBall shiftRadius,
      family (center + offset.val) ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level)
    (offset : PlaneMatrix) : analyticStage data level coefficientRadius positiveRadius :=
  if membership : ‖offset‖₊ ≤ shiftRadius then
    localStageFamily data level family center series expansionRadius expansion shiftRadius coefficientRadius
      positiveRadius radiusBound fixed ⟨offset, membership⟩
  else 0

theorem stageFamily_val (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (family : PlaneMatrix → data.H) (center : PlaneMatrix)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (familyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < expansionRadius)
    (fixed : ∀ offset : ParameterBall shiftRadius,
      family (center + offset.val) ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level)
    (offset : PlaneMatrix) (membership : ‖offset‖₊ ≤ shiftRadius) :
    (stageFamily data level family center series expansionRadius expansion shiftRadius coefficientRadius
      positiveRadius radiusBound fixed offset).val =
      (family (center + offset), coefficients data series shiftRadius coefficientRadius (radiusBound.trans_le expansion.r_le) offset) := by
  rw [stageFamily, dite_eq_left membership, coefficients_eq data series shiftRadius coefficientRadius _ offset membership]
  rfl

theorem family_analyticOnNhd (data : CuspidalRepresentation) (family : PlaneMatrix → data.H)
    (center : PlaneMatrix) (series : FormalMultilinearSeries ℝ JointMatrix data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (familyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius : ℝ≥0) (shiftBound : (shiftRadius : ENNReal) < expansionRadius) :
    AnalyticOnNhd ℝ (fun offset => family (center + offset)) (Metric.eball 0 (shiftRadius : ENNReal)) := by
  intro offset membership
  have inserted : ((1 : BinaryMatrix), center + offset) ∈ Metric.eball (1, center) expansionRadius := by
    have distanceEquality : edist ((1 : BinaryMatrix), center + offset) (1, center) = edist offset 0 := by
      rw [Prod.edist_eq, edist_self, max_eq_right zero_le]
      simpa only [add_zero] using edist_add_left center offset (0 : PlaneMatrix)
    rw [Metric.mem_eball, distanceEquality]
    exact (Metric.mem_eball.mp membership).trans shiftBound
  have insertion : AnalyticAt ℝ (fun offset : PlaneMatrix => ((1 : BinaryMatrix), center + offset)) offset :=
    analyticAt_const.prod (analyticAt_const.add analyticAt_id)
  have composite := (expansion.analyticOnNhd _ inserted).comp
    (f := fun point : PlaneMatrix => ((1 : BinaryMatrix), center + point)) insertion
  have equality : (fun offset : PlaneMatrix => familyOrbit data family (1, center + offset)) =
      (fun offset => family (center + offset)) := by
    funext offset
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.realOrbit_one data _
  exact equality ▸ composite

theorem stageFamily_analyticOnNhd (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (family : PlaneMatrix → data.H) (center : PlaneMatrix)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (familyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveShift : 0 < shiftRadius) (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < expansionRadius)
    (fixed : ∀ offset : ParameterBall shiftRadius,
      family (center + offset.val) ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level) :
    AnalyticOnNhd ℝ (stageFamily data level family center series expansionRadius expansion shiftRadius coefficientRadius
      positiveRadius radiusBound fixed) (Metric.eball 0 (shiftRadius : ENNReal)) := by
  intro offset membership
  apply ClosedSubspaceAnalytic.analyticAt ((analyticStage data level coefficientRadius positiveRadius).restrictScalars ℝ)
    (analyticStage_isClosed data level coefficientRadius positiveRadius)
  have analytic := ((family_analyticOnNhd data family center series expansionRadius expansion shiftRadius
    ((le_add_right le_rfl).trans_lt radiusBound)) offset membership).prod
    ((coefficients_analyticOnNhd data series shiftRadius coefficientRadius positiveShift
      (radiusBound.trans_le expansion.r_le)) offset membership)
  apply analytic.congr
  filter_upwards [Metric.isOpen_eball.mem_nhds membership] with point inside
  have bound : ‖point‖₊ ≤ shiftRadius := by
    have strict : ‖point‖₊ < shiftRadius := by
      simpa only [Metric.mem_eball, edist_lt_coe, nndist_zero_right] using inside
    exact strict.le
  exact (stageFamily_val data level family center series expansionRadius expansion shiftRadius coefficientRadius
    positiveRadius radiusBound fixed point bound).symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStageFamilies
