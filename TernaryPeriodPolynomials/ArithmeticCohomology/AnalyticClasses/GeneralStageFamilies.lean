module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.LocalAnalyticFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Realization
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Scalar

@[expose] public section


/-!
# Local analytic stage families over an arbitrary parameter space

`PlaneEisensteinContinuation.LocalAnalyticFamilies` lifts a family of Hilbert vectors indexed by
one `3 × 3` real matrix, whose `GL₂(ℝ)`-orbit is jointly analytic, locally and continuously into a
single analytic stage. This file is the same construction with the parameter space replaced by an
arbitrary real normed space `E` (ported from that file; only the parameter type changes). Combined
with continuity of the stage realizations, it shows that the cusp sup norm of such a family is
continuous, hence bounded on compact parameter sets. This is the uniformity needed for source
cochains whose vertices vary in a compact set.

Original work by Claude Opus 5.5 (AxiomCode), adapting
`TernaryPeriodPolynomials.PlaneEisensteinContinuation.LocalAnalyticFamilies`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.TranslatedSeries
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientRestriction
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.AnalyticClasses

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed parameter ball of radius `radius` in `E`. -/
abbrev GeneralBall (E : Type) [NormedAddCommGroup E] (radius : ℝ≥0) := {offset : E // ‖offset‖₊ ≤ radius}

omit [NormedSpace ℝ E] in
theorem continuousAt_of_generalBall {Target : Type} [TopologicalSpace Target]
    (function : E → Target) (center : E) (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (continuity : Continuous (fun offset : GeneralBall E radius => function (center + offset.val))) :
    ContinuousAt function center := by
  have continuityOn : ContinuousOn (fun offset : E => function (center + offset))
      {offset | ‖offset‖₊ ≤ radius} := continuousOn_iff_continuous_domRestrict.mpr continuity
  have ballEquality : {offset : E | ‖offset‖₊ ≤ radius} = Metric.closedBall 0 (radius : ℝ) := by
    ext offset
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    exact NNReal.coe_le_coe.symm
  have neighborhood : {offset : E | ‖offset‖₊ ≤ radius} ∈ nhds (0 : E) := by
    rw [ballEquality]
    exact Metric.closedBall_mem_nhds _ (by exact_mod_cast positiveRadius)
  have zeroContinuity := continuityOn.continuousAt neighborhood
  have shiftedContinuity : ContinuousAt (fun offset : E => function (center + offset)) (center - center) := by
    simpa only [sub_self] using zeroContinuity
  have subtractContinuous : ContinuousAt (fun point : E => point - center) center :=
    continuousAt_id.sub continuousAt_const
  have composite := shiftedContinuity.comp (f := fun point : E => point - center) subtractContinuous
  convert composite using 1
  funext point
  congr 1
  exact (sub_add_cancel point center).symm.trans (add_comm _ _)

/-- Embed a parameter offset as a joint offset with zero `GL₂` part. -/
noncomputable def generalShift (radius : ℝ≥0) (offset : GeneralBall E radius) :
    {offset : BinaryMatrix × E // ‖offset‖₊ ≤ radius} :=
  ⟨(0, offset.val), by simpa only [Prod.nnnorm_mk, nnnorm_zero, zero_le, max_eq_right] using offset.property⟩

omit [NormedSpace ℝ E] in
theorem generalShift_continuous (radius : ℝ≥0) : Continuous (generalShift (E := E) radius) :=
  (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- The `GL₂`-orbit of a family of vectors, as a function of the joint variable. -/
noncomputable def generalFamilyOrbit (data : CuspidalRepresentation) (family : E → data.H)
    (matrices : BinaryMatrix × E) : data.H := realOrbit data (family matrices.2) matrices.1

noncomputable def generalLocalCoefficients (data : CuspidalRepresentation)
    (series : FormalMultilinearSeries ℝ (BinaryMatrix × E) data.H) (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : GeneralBall E shiftRadius) : CoefficientSpace data :=
  restrictCoefficients (ContinuousLinearMap.inl ℝ BinaryMatrix E)
    (ContinuousLinearMap.norm_inl_le_one ℝ BinaryMatrix E)
    (translatedCoefficients series shiftRadius coefficientRadius radiusBound (generalShift shiftRadius offset))

theorem generalLocalCoefficients_continuous (data : CuspidalRepresentation)
    (series : FormalMultilinearSeries ℝ (BinaryMatrix × E) data.H) (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius) :
    Continuous (generalLocalCoefficients data series shiftRadius coefficientRadius radiusBound) :=
  (restrictCoefficients (Target := data.H) (ContinuousLinearMap.inl ℝ BinaryMatrix E)
    (ContinuousLinearMap.norm_inl_le_one ℝ BinaryMatrix E)).continuous.comp
      ((translatedCoefficients_continuous series shiftRadius coefficientRadius radiusBound).comp
        (generalShift_continuous shiftRadius))

theorem weighted_generalLocalCoefficients_apply (data : CuspidalRepresentation)
    (series : FormalMultilinearSeries ℝ (BinaryMatrix × E) data.H) (shiftRadius coefficientRadius : ℝ≥0)
    (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : GeneralBall E shiftRadius) (order : ℕ) (directions : Fin order → BinaryMatrix) :
    weightedSeries data coefficientRadius
      (generalLocalCoefficients data series shiftRadius coefficientRadius radiusBound offset) order directions =
      series.changeOrigin (0, offset.val) order (fun index => (directions index, 0)) := by
  change ((coefficientRadius : ℝ)⁻¹ ^ order) • ((coefficientRadius : ℝ) ^ order •
    series.changeOrigin (0, offset.val) order (fun index => (directions index, 0))) = _
  have radiusNonzero : (coefficientRadius : ℝ) ≠ 0 := by exact_mod_cast positiveRadius.ne'
  rw [smul_smul, ← mul_pow, inv_mul_cancel₀ radiusNonzero, one_pow, one_smul]

theorem general_family_continuous (data : CuspidalRepresentation) (family : E → data.H)
    (center : E) (series : FormalMultilinearSeries ℝ (BinaryMatrix × E) data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (generalFamilyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius : ℝ≥0) (shiftBound : (shiftRadius : ENNReal) < expansionRadius) :
    Continuous (fun offset : GeneralBall E shiftRadius => family (center + offset.val)) := by
  have insertContinuous : Continuous (fun offset : GeneralBall E shiftRadius =>
      ((1 : BinaryMatrix), center) + ((0 : BinaryMatrix), offset.val)) :=
    continuous_const.add (continuous_const.prodMk continuous_subtype_val)
  have orbitContinuous := expansion.continuousOn.comp_continuous insertContinuous (fun offset => by
    have normBound : (‖((0 : BinaryMatrix), offset.val)‖₊ : ENNReal) < expansionRadius := by
      simpa only [Prod.nnnorm_mk, nnnorm_zero, zero_le, max_eq_right] using
        (ENNReal.coe_le_coe.mpr offset.property).trans_lt shiftBound
    have distanceEquality : edist (((1 : BinaryMatrix), center) + ((0 : BinaryMatrix), offset.val))
        ((1 : BinaryMatrix), center) = edist ((0 : BinaryMatrix), offset.val) (0 : BinaryMatrix × E) := by
      simpa only [add_zero] using edist_add_left ((1 : BinaryMatrix), center)
        ((0 : BinaryMatrix), offset.val) (0 : BinaryMatrix × E)
    simpa only [Metric.mem_eball, distanceEquality, edist_nndist, nndist_zero_right] using normBound)
  have equality : (fun offset : GeneralBall E shiftRadius =>
      generalFamilyOrbit data family (((1 : BinaryMatrix), center) + ((0 : BinaryMatrix), offset.val))) =
      (fun offset => family (center + offset.val)) := by
    funext offset
    change realOrbit data (family (center + offset.val)) (1 + 0) = family (center + offset.val)
    rw [add_zero]
    exact AnalyticOrbit.realOrbit_one data _
  exact equality ▸ orbitContinuous

theorem general_family_expansion (data : CuspidalRepresentation) (family : E → data.H)
    (center : E) (series : FormalMultilinearSeries ℝ (BinaryMatrix × E) data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (generalFamilyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < expansionRadius)
    (offset : GeneralBall E shiftRadius) :
    HasFPowerSeriesOnBall (realOrbit data (family (center + offset.val)))
      (weightedSeries data coefficientRadius (generalLocalCoefficients data series shiftRadius coefficientRadius
        (radiusBound.trans_le expansion.r_le) offset)) 1 ((coefficientRadius / 2 : ℝ≥0) : ENNReal) := by
  have halfLe : ((coefficientRadius / 2 : ℝ≥0) : ENNReal) ≤ (coefficientRadius : ENNReal) := by
    exact_mod_cast (div_le_self (show (0 : ℝ≥0) ≤ coefficientRadius from zero_le) (show (1 : ℝ≥0) ≤ 2 by norm_num))
  have shiftNorm : ‖((0 : BinaryMatrix), offset.val)‖₊ ≤ shiftRadius :=
    (generalShift shiftRadius offset).property
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
  have jointMembership : ((direction, (0 : E)) : BinaryMatrix × E) ∈
      Metric.eball 0 ((coefficientRadius / 2 : ℝ≥0) : ENNReal) := by
    simpa only [Metric.mem_eball, edist_nndist, nndist_zero_right, Prod.nnnorm_mk,
      nnnorm_zero, zero_le, max_eq_left] using membership
  have sum := shifted.hasSum jointMembership
  have termEquality : (fun order => weightedSeries data coefficientRadius
      (generalLocalCoefficients data series shiftRadius coefficientRadius (radiusBound.trans_le expansion.r_le) offset)
      order (fun _ => direction)) =
      (fun order => series.changeOrigin (0, offset.val) order (fun _ => (direction, (0 : E)))) := by
    funext order
    exact weighted_generalLocalCoefficients_apply data series shiftRadius coefficientRadius positiveRadius
      (radiusBound.trans_le expansion.r_le) offset order (fun _ => direction)
  apply (congrArg (fun summand : ℕ → data.H =>
    HasSum summand (realOrbit data (family (center + offset.val)) (1 + direction))) termEquality).mpr
  convert sum using 1
  change realOrbit data (family (center + offset.val)) (1 + direction) =
    realOrbit data (family ((center + offset.val) + 0)) ((1 + 0) + direction)
  rw [add_zero, add_zero]

/-- The local continuous lift of the family into one analytic stage. -/
noncomputable def generalStageFamily (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (family : E → data.H) (center : E)
    (series : FormalMultilinearSeries ℝ (BinaryMatrix × E) data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (generalFamilyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < expansionRadius)
    (fixed : ∀ offset : GeneralBall E shiftRadius, family (center + offset.val) ∈ BinaryLevel.fixedSubspace data level)
    (offset : GeneralBall E shiftRadius) : analyticStage data level coefficientRadius positiveRadius :=
  ⟨(family (center + offset.val), generalLocalCoefficients data series shiftRadius coefficientRadius
      (radiusBound.trans_le expansion.r_le) offset),
    fixed offset, general_family_expansion data family center series expansionRadius expansion
      shiftRadius coefficientRadius positiveRadius radiusBound offset⟩

theorem generalStageFamily_continuous (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (family : E → data.H) (center : E)
    (series : FormalMultilinearSeries ℝ (BinaryMatrix × E) data.H) (expansionRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (generalFamilyOrbit data family) series (1, center) expansionRadius)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveRadius : 0 < coefficientRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < expansionRadius)
    (fixed : ∀ offset : GeneralBall E shiftRadius, family (center + offset.val) ∈ BinaryLevel.fixedSubspace data level) :
    Continuous (generalStageFamily data level family center series expansionRadius expansion
      shiftRadius coefficientRadius positiveRadius radiusBound fixed) :=
  ((general_family_continuous data family center series expansionRadius expansion shiftRadius
      ((le_add_right le_rfl).trans_lt radiusBound)).prodMk
    (generalLocalCoefficients_continuous data series shiftRadius coefficientRadius
      (radiusBound.trans_le expansion.r_le))).subtype_mk _

/-- **Continuity of the cusp sup norm along a jointly analytic family.** If the `GL₂(ℝ)`-orbit of a
family of finite-level fixed smooth vectors is jointly analytic at `(1, center)`, then its cusp sup
norm is continuous at `center` (given continuity of the stage realizations). -/
theorem cuspSupNorm_continuousAt_of_jointAnalytic (data : CuspidalRepresentation)
    (stageContinuity : AnalyticScalar.ContinuousStages data)
    (family : E → data.smooth) (center : E)
    (analytic : AnalyticAt ℝ (generalFamilyOrbit data (fun point => (family point).val)) (1, center))
    (fixed : ∀ point, (family point).val ∈ BinaryLevel.fixedSubspace data finiteCongruence) :
    ContinuousAt (fun point => CuspSupNorm.cuspSupNorm (family point)) center := by
  obtain ⟨series, expansionRadius, expansion⟩ := analytic
  obtain ⟨radius, positiveRadius, radiusBound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp expansion.r_pos
  have radiusPositive : (0 : ℝ≥0) < radius := by exact_mod_cast positiveRadius
  have halfPositive : (0 : ℝ≥0) < radius / 2 := div_pos radiusPositive (by norm_num)
  have halfBound : ((radius / 2 : ℝ≥0) : ENNReal) + ((radius / 2 : ℝ≥0) : ENNReal) < expansionRadius := by
    rw [← ENNReal.coe_add, add_halves]
    exact radiusBound
  let lift := generalStageFamily data finiteCongruence (fun point => (family point).val) center series
    expansionRadius expansion (radius / 2) (radius / 2) halfPositive halfBound (fun offset => fixed _)
  have liftContinuous : Continuous lift :=
    generalStageFamily_continuous data finiteCongruence (fun point => (family point).val) center series
      expansionRadius expansion (radius / 2) (radius / 2) halfPositive halfBound (fun offset => fixed _)
  have realizationContinuous := (stageContinuity (radius / 2) halfPositive).comp liftContinuous
  have normContinuous := realizationContinuous.norm
  have equality : (fun offset : GeneralBall E (radius / 2) =>
      ‖AnalyticRealization.stageRealization data finiteCongruence finiteCongruence_isOpen
        finiteCongruence_isCompact (radius / 2) halfPositive (lift offset)‖) =
      (fun offset => CuspSupNorm.cuspSupNorm (family (center + offset.val))) := by
    funext offset
    change CuspSupNorm.cuspSupNorm (stageSmoothMap data finiteCongruence
      finiteCongruence_isOpen finiteCongruence_isCompact (radius / 2) halfPositive (lift offset)).val = _
    apply congrArg CuspSupNorm.cuspSupNorm
    exact Subtype.ext rfl
  exact continuousAt_of_generalBall _ center (radius / 2) halfPositive (equality ▸ normContinuous)


/-- **Continuity of the bounded realization along a jointly analytic family** (sup-norm valued). -/
theorem boundedRealization_continuousAt_of_jointAnalytic (data : CuspidalRepresentation)
    (stageContinuity : AnalyticScalar.ContinuousStages data)
    (family : E → data.smooth) (center : E)
    (analytic : AnalyticAt ℝ (generalFamilyOrbit data (fun point => (family point).val)) (1, center))
    (fixed : ∀ point, (family point).val ∈ BinaryLevel.fixedSubspace data finiteCongruence) :
    ContinuousAt (fun point => CuspSupNorm.boundedRealization data (family point)) center := by
  obtain ⟨series, expansionRadius, expansion⟩ := analytic
  obtain ⟨radius, positiveRadius, radiusBound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp expansion.r_pos
  have radiusPositive : (0 : ℝ≥0) < radius := by exact_mod_cast positiveRadius
  have halfPositive : (0 : ℝ≥0) < radius / 2 := div_pos radiusPositive (by norm_num)
  have halfBound : ((radius / 2 : ℝ≥0) : ENNReal) + ((radius / 2 : ℝ≥0) : ENNReal) < expansionRadius := by
    rw [← ENNReal.coe_add, add_halves]
    exact radiusBound
  let lift := generalStageFamily data finiteCongruence (fun point => (family point).val) center series
    expansionRadius expansion (radius / 2) (radius / 2) halfPositive halfBound (fun offset => fixed _)
  have liftContinuous : Continuous lift :=
    generalStageFamily_continuous data finiteCongruence (fun point => (family point).val) center series
      expansionRadius expansion (radius / 2) (radius / 2) halfPositive halfBound (fun offset => fixed _)
  have realizationContinuous := (stageContinuity (radius / 2) halfPositive).comp liftContinuous
  have equality : (fun offset : GeneralBall E (radius / 2) =>
      AnalyticRealization.stageRealization data finiteCongruence finiteCongruence_isOpen
        finiteCongruence_isCompact (radius / 2) halfPositive (lift offset)) =
      (fun offset => CuspSupNorm.boundedRealization data (family (center + offset.val))) := by
    funext offset
    change CuspSupNorm.boundedRealization data (stageSmoothMap data finiteCongruence
      finiteCongruence_isOpen finiteCongruence_isCompact (radius / 2) halfPositive (lift offset)).val = _
    apply congrArg (CuspSupNorm.boundedRealization data)
    exact Subtype.ext rfl
  exact continuousAt_of_generalBall _ center (radius / 2) halfPositive (equality ▸ realizationContinuous)

end TernaryPeriodPolynomials.AnalyticClasses
