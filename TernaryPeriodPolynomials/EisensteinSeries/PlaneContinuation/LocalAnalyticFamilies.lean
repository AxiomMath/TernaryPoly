module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Coefficient.Restriction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.TranslatedSeries TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientRestriction
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.LocalAnalyticFamilies

abbrev ParameterBall (radius : ℝ≥0) := {offset : PlaneMatrix // ‖offset‖₊ ≤ radius}

theorem continuousAt_of_parameterBall {Target : Type} [TopologicalSpace Target]
    (function : PlaneMatrix → Target) (center : PlaneMatrix) (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (continuity : Continuous (fun offset : ParameterBall radius => function (center + offset.val))) :
    ContinuousAt function center := by
  have continuityOn : ContinuousOn (fun offset : PlaneMatrix => function (center + offset))
      {offset | ‖offset‖₊ ≤ radius} := continuousOn_iff_continuous_domRestrict.mpr continuity
  have ballEquality : {offset : PlaneMatrix | ‖offset‖₊ ≤ radius} = Metric.closedBall 0 (radius : ℝ) := by
    ext offset
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    exact NNReal.coe_le_coe.symm
  have neighborhood : {offset : PlaneMatrix | ‖offset‖₊ ≤ radius} ∈ nhds (0 : PlaneMatrix) := by
    rw [ballEquality]
    exact Metric.closedBall_mem_nhds _ (by exact_mod_cast positiveRadius)
  have zeroContinuity := continuityOn.continuousAt neighborhood
  have shiftedContinuity : ContinuousAt (fun offset : PlaneMatrix => function (center + offset)) (center - center) := by
    simpa only [sub_self] using zeroContinuity
  have subtractContinuous : ContinuousAt (fun matrix : PlaneMatrix => matrix - center) center :=
    continuousAt_id.sub continuousAt_const
  have composite := shiftedContinuity.comp (f := fun matrix : PlaneMatrix => matrix - center) subtractContinuous
  convert composite using 1
  funext matrix
  congr 1
  exact (sub_add_cancel matrix center).symm.trans (add_comm _ _)

noncomputable def jointShift (radius : ℝ≥0) (offset : ParameterBall radius) :
    {offset : JointMatrix // ‖offset‖₊ ≤ radius} :=
  ⟨(0, offset.val), by simpa only [Prod.nnnorm_mk, nnnorm_zero, zero_le, max_eq_right] using offset.property⟩

theorem jointShift_continuous (radius : ℝ≥0) : Continuous (jointShift radius) :=
  (continuous_const.prodMk continuous_subtype_val).subtype_mk _

noncomputable def localCoefficients (data : CuspidalRepresentation)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : ParameterBall shiftRadius) : CoefficientSpace data :=
  restrictCoefficients (ContinuousLinearMap.inl ℝ BinaryMatrix PlaneMatrix)
    (ContinuousLinearMap.norm_inl_le_one ℝ BinaryMatrix PlaneMatrix)
    (translatedCoefficients series shiftRadius coefficientRadius radiusBound (jointShift shiftRadius offset))

theorem localCoefficients_continuous (data : CuspidalRepresentation)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius) :
    Continuous (localCoefficients data series shiftRadius coefficientRadius radiusBound) :=
  (restrictCoefficients (Target := data.H) (ContinuousLinearMap.inl ℝ BinaryMatrix PlaneMatrix)
    (ContinuousLinearMap.norm_inl_le_one ℝ BinaryMatrix PlaneMatrix)).continuous.comp
      ((translatedCoefficients_continuous series shiftRadius coefficientRadius radiusBound).comp
        (jointShift_continuous shiftRadius))

theorem weighted_localCoefficients_apply (data : CuspidalRepresentation)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (shiftRadius coefficientRadius : ℝ≥0)
    (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : ParameterBall shiftRadius) (order : ℕ) (directions : Fin order → BinaryMatrix) :
    weightedSeries data coefficientRadius
      (localCoefficients data series shiftRadius coefficientRadius radiusBound offset) order directions =
      series.changeOrigin (0, offset.val) order (fun index => (directions index, 0)) := by
  change ((coefficientRadius : ℝ)⁻¹ ^ order) • ((coefficientRadius : ℝ) ^ order •
    series.changeOrigin (0, offset.val) order (fun index => (directions index, 0))) = _
  have radiusNonzero : (coefficientRadius : ℝ) ≠ 0 := by exact_mod_cast positiveRadius.ne'
  rw [smul_smul, ← mul_pow, inv_mul_cancel₀ radiusNonzero, one_pow, one_smul]

noncomputable def familyOrbit (data : CuspidalRepresentation) (family : PlaneMatrix → data.H)
    (matrices : JointMatrix) : data.H := realOrbit data (family matrices.2) matrices.1

theorem local_family_continuous (data : CuspidalRepresentation) (family : PlaneMatrix → data.H)
    (center : PlaneMatrix) (series : FormalMultilinearSeries ℝ JointMatrix data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (familyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius : ℝ≥0) (shiftBound : (shiftRadius : ENNReal) < expansionRadius) :
    Continuous (fun offset : ParameterBall shiftRadius => family (center + offset.val)) := by
  have insertContinuous : Continuous (fun offset : ParameterBall shiftRadius =>
      (1, center) + (0, offset.val) : ParameterBall shiftRadius → JointMatrix) :=
    continuous_const.add (continuous_const.prodMk continuous_subtype_val)
  have orbitContinuous := expansion.continuousOn.comp_continuous insertContinuous (fun offset => by
    have normBound : (‖((0 : BinaryMatrix), offset.val)‖₊ : ENNReal) < expansionRadius := by
      simpa only [Prod.nnnorm_mk, nnnorm_zero, zero_le, max_eq_right] using
        (ENNReal.coe_le_coe.mpr offset.property).trans_lt shiftBound
    have distanceEquality : edist ((1, center) + ((0 : BinaryMatrix), offset.val)) (1, center) =
        edist ((0 : BinaryMatrix), offset.val) (0 : JointMatrix) := by
      simpa only [add_zero] using edist_add_left ((1 : BinaryMatrix), center)
        ((0 : BinaryMatrix), offset.val) (0 : JointMatrix)
    simpa only [Metric.mem_eball, distanceEquality, edist_nndist, nndist_zero_right] using normBound)
  have equality : (fun offset : ParameterBall shiftRadius =>
      familyOrbit data family ((1, center) + (0, offset.val))) =
      (fun offset => family (center + offset.val)) := by
    funext offset
    change realOrbit data (family (center + offset.val)) (1 + 0) = family (center + offset.val)
    rw [add_zero]
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.realOrbit_one data _
  exact equality ▸ orbitContinuous

theorem local_family_expansion (data : CuspidalRepresentation) (family : PlaneMatrix → data.H)
    (center : PlaneMatrix) (series : FormalMultilinearSeries ℝ JointMatrix data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (familyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < expansionRadius)
    (offset : ParameterBall shiftRadius) :
    HasFPowerSeriesOnBall (realOrbit data (family (center + offset.val)))
      (weightedSeries data coefficientRadius (localCoefficients data series shiftRadius coefficientRadius
        (radiusBound.trans_le expansion.r_le) offset)) 1 ((coefficientRadius / 2 : ℝ≥0) : ENNReal) := by
  have halfLe : ((coefficientRadius / 2 : ℝ≥0) : ENNReal) ≤ (coefficientRadius : ENNReal) := by
    exact_mod_cast (div_le_self (show (0 : ℝ≥0) ≤ coefficientRadius from zero_le) (show (1 : ℝ≥0) ≤ 2 by norm_num))
  have shiftNorm : ‖((0 : BinaryMatrix), offset.val)‖₊ ≤ shiftRadius :=
    (jointShift shiftRadius offset).property
  have shiftLt : (‖((0 : BinaryMatrix), offset.val)‖₊ : ENNReal) < expansionRadius :=
    (ENNReal.coe_le_coe.mpr shiftNorm).trans_lt ((le_add_right le_rfl).trans_lt radiusBound)
  have remainingRadius : (coefficientRadius : ENNReal) ≤
      expansionRadius - (‖((0 : BinaryMatrix), offset.val)‖₊ : ENNReal) := by
    apply ENNReal.le_sub_of_add_le_left ENNReal.coe_ne_top
    exact ((add_le_add (ENNReal.coe_le_coe.mpr shiftNorm) le_rfl).trans_lt radiusBound).le
  have shifted := (expansion.changeOrigin shiftLt).mono (halfRadius_pos coefficientRadius positiveRadius)
    (halfLe.trans remainingRadius)
  refine ⟨halfLe.trans (weightedSeries_radius_ge data coefficientRadius positiveRadius _),
    halfRadius_pos coefficientRadius positiveRadius, ?_⟩
  intro direction membership
  have jointMembership : ((direction, (0 : PlaneMatrix)) : JointMatrix) ∈
      Metric.eball 0 ((coefficientRadius / 2 : ℝ≥0) : ENNReal) := by
    simpa only [Metric.mem_eball, edist_nndist, nndist_zero_right, Prod.nnnorm_mk,
      nnnorm_zero, zero_le, max_eq_left] using membership
  have sum := shifted.hasSum jointMembership
  have termEquality : (fun order => weightedSeries data coefficientRadius
      (localCoefficients data series shiftRadius coefficientRadius (radiusBound.trans_le expansion.r_le) offset)
      order (fun _ => direction)) =
      (fun order => series.changeOrigin (0, offset.val) order (fun _ => (direction, (0 : PlaneMatrix)))) := by
    funext order
    exact weighted_localCoefficients_apply data series shiftRadius coefficientRadius positiveRadius
      (radiusBound.trans_le expansion.r_le) offset order (fun _ => direction)
  apply (congrArg (fun summand : ℕ → data.H =>
    HasSum summand (realOrbit data (family (center + offset.val)) (1 + direction))) termEquality).mpr
  convert sum using 1
  change realOrbit data (family (center + offset.val)) (1 + direction) =
    realOrbit data (family ((center + offset.val) + 0)) ((1 + 0) + direction)
  rw [add_zero, add_zero]

noncomputable def localStageFamily (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (family : PlaneMatrix → data.H) (center : PlaneMatrix)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (familyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < expansionRadius)
    (fixed : ∀ offset : ParameterBall shiftRadius,
      family (center + offset.val) ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level)
    (offset : ParameterBall shiftRadius) : analyticStage data level coefficientRadius positiveRadius :=
  ⟨(family (center + offset.val), localCoefficients data series shiftRadius coefficientRadius
      (radiusBound.trans_le expansion.r_le) offset),
    fixed offset, local_family_expansion data family center series expansionRadius expansion
      shiftRadius coefficientRadius positiveRadius radiusBound offset⟩

theorem localStageFamily_continuous (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (family : PlaneMatrix → data.H) (center : PlaneMatrix)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (familyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < expansionRadius)
    (fixed : ∀ offset : ParameterBall shiftRadius,
      family (center + offset.val) ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level) :
    Continuous (localStageFamily data level family center series expansionRadius expansion
      shiftRadius coefficientRadius positiveRadius radiusBound fixed) :=
  ((local_family_continuous data family center series expansionRadius expansion shiftRadius
      ((le_add_right le_rfl).trans_lt radiusBound)).prodMk
    (localCoefficients_continuous data series shiftRadius coefficientRadius
      (radiusBound.trans_le expansion.r_le))).subtype_mk _

theorem stageHilbertMap_localStageFamily (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (family : PlaneMatrix → data.H) (center : PlaneMatrix)
    (series : FormalMultilinearSeries ℝ JointMatrix data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (familyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < expansionRadius)
    (fixed : ∀ offset : ParameterBall shiftRadius,
      family (center + offset.val) ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level)
    (offset : ParameterBall shiftRadius) :
    stageHilbertMap data level coefficientRadius positiveRadius
      (localStageFamily data level family center series expansionRadius expansion
        shiftRadius coefficientRadius positiveRadius radiusBound fixed offset) =
      family (center + offset.val) := rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.LocalAnalyticFamilies
