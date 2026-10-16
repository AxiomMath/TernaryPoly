module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Limits
public import Mathlib.Analysis.Normed.Lp.lpSpace

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticLimits
open scoped Matrix.Norms.Elementwise NNReal
open Filter

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages

noncomputable abbrev CoefficientSpace (data : CuspidalRepresentation) : Type :=
  lp (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H) ⊤

noncomputable def weightedSeries (data : CuspidalRepresentation) (radius : ℝ≥0) :
    CoefficientSpace data →ₗ[ℂ] FormalMultilinearSeries ℝ BinaryMatrix data.H where
  toFun coefficients order := ((radius : ℝ)⁻¹ ^ order) • coefficients order
  map_add' first second := by
    funext order
    change ((radius : ℝ)⁻¹ ^ order) • ((first + second) order) =
      ((radius : ℝ)⁻¹ ^ order) • first order + ((radius : ℝ)⁻¹ ^ order) • second order
    exact smul_add _ _ _
  map_smul' scalar coefficients := by
    funext order
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    apply ContinuousMultilinearMap.ext
    intro directions
    exact smul_comm _ _ _

theorem weightedSeries_norm_bound (data : CuspidalRepresentation) (radius : ℝ≥0)
    (coefficients : CoefficientSpace data) (order : ℕ) :
    ‖weightedSeries data radius coefficients order‖ ≤ ‖coefficients‖ * (radius : ℝ)⁻¹ ^ order := by
  change ‖((radius : ℝ)⁻¹ ^ order) • coefficients order‖ ≤ _
  calc
    _ = ((radius : ℝ)⁻¹ ^ order) * ‖coefficients order‖ :=
      (norm_smul _ _).trans (congrArg (fun value : ℝ => value * ‖coefficients order‖)
        (Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr radius.property) order)))
    _ ≤ ((radius : ℝ)⁻¹ ^ order) * ‖coefficients‖ :=
      mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) coefficients order)
        (pow_nonneg (inv_nonneg.mpr radius.property) order)
    _ = _ := mul_comm _ _

theorem weightedSeries_radius_ge (data : CuspidalRepresentation) (radius : ℝ≥0)
    (positiveRadius : 0 < radius) (coefficients : CoefficientSpace data) :
    (radius : ENNReal) ≤ (weightedSeries data radius coefficients).radius := by
  have radiusNonzero : (radius : ℝ) ≠ 0 := by exact_mod_cast positiveRadius.ne'
  apply (weightedSeries data radius coefficients).le_radius_of_bound ‖coefficients‖
  intro order
  calc
    _ ≤ (‖coefficients‖ * (radius : ℝ)⁻¹ ^ order) * (radius : ℝ) ^ order :=
      mul_le_mul_of_nonneg_right (weightedSeries_norm_bound data radius coefficients order)
        (pow_nonneg radius.property order)
    _ = ‖coefficients‖ := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ radiusNonzero, one_pow, mul_one]

noncomputable def weightedCoefficient (data : CuspidalRepresentation) (radius : ℝ≥0) (order : ℕ) :
    CoefficientSpace data →L[ℂ] ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H :=
  ((LinearMap.proj order).comp (weightedSeries data radius)).mkContinuous ((radius : ℝ)⁻¹ ^ order)
    (fun coefficients => (weightedSeries_norm_bound data radius coefficients order).trans_eq (mul_comm _ _))

noncomputable def realOrbitLinear (data : CuspidalRepresentation) : data.H →ₗ[ℂ] (BinaryMatrix → data.H) where
  toFun := realOrbit data
  map_add' first second := funext (fun matrix => map_add (data.π (atInfinity (invertibleMatrix matrix))) first second)
  map_smul' scalar vector := funext (fun matrix => map_smul (data.π (atInfinity (invertibleMatrix matrix))) scalar vector)

theorem halfRadius_pos (radius : ℝ≥0) (positiveRadius : 0 < radius) :
    0 < ((radius / 2 : ℝ≥0) : ENNReal) := by
  exact_mod_cast div_pos positiveRadius (show (0 : ℝ≥0) < 2 by norm_num)

theorem halfRadius_bound (radius : ℝ≥0) (positiveRadius : 0 < radius) :
    (radius : ℝ)⁻¹ * ((radius / 2 : ℝ≥0) : ℝ) < 1 := by
  have positiveRealRadius : (0 : ℝ) < radius := by exact_mod_cast positiveRadius
  simp only [NNReal.coe_div, NNReal.coe_ofNat]
  rw [← mul_div_assoc, inv_mul_cancel₀ positiveRealRadius.ne']
  norm_num

/-- A fixed radius Banach model retains the vector and a bounded sequence of scaled coefficients. -/
noncomputable def analyticStage (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (radius : ℝ≥0) (positiveRadius : 0 < radius) : Submodule ℂ (data.H × CoefficientSpace data) where
  carrier := {pair | pair.1 ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level ∧
    HasFPowerSeriesOnBall (realOrbitLinear data pair.1) (weightedSeries data radius pair.2)
      1 ((radius / 2 : ℝ≥0) : ENNReal)}
  zero_mem' := by
    refine ⟨(TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level).zero_mem, ?_⟩
    change HasFPowerSeriesOnBall (realOrbitLinear data 0) (weightedSeries data radius 0) _ _
    rw [map_zero, map_zero]
    refine ⟨?_, halfRadius_pos radius positiveRadius, ?_⟩
    · apply (0 : FormalMultilinearSeries ℝ BinaryMatrix data.H).le_radius_of_bound 0
      intro order
      have zeroNorm : ‖(0 : ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H)‖ = 0 := norm_zero
      exact le_of_eq ((congrArg (fun value : ℝ => value * ((radius / 2 : ℝ≥0) : ℝ) ^ order)
        zeroNorm).trans (zero_mul _))
    intro offset _
    exact hasSum_zero
  add_mem' := by
    intro first second firstMem secondMem
    refine ⟨(TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level).add_mem firstMem.1 secondMem.1, ?_⟩
    change HasFPowerSeriesOnBall (realOrbitLinear data (first.1 + second.1))
      (weightedSeries data radius (first.2 + second.2)) _ _
    rw [map_add, map_add]
    exact firstMem.2.add secondMem.2
  smul_mem' := by
    intro scalar pair membership
    refine ⟨(TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level).smul_mem scalar membership.1, ?_⟩
    change HasFPowerSeriesOnBall (realOrbitLinear data (scalar • pair.1))
      (weightedSeries data radius (scalar • pair.2)) _ _
    rw [map_smul, map_smul]
    exact membership.2.const_smul

theorem analyticStage_isClosed (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (radius : ℝ≥0) (positiveRadius : 0 < radius) :
    IsClosed (analyticStage data level radius positiveRadius : Set (data.H × CoefficientSpace data)) := by
  apply IsSeqClosed.isClosed
  intro sequence limitPair membership convergence
  have vectorConvergence : Tendsto (fun index => (sequence index).1) atTop (nhds limitPair.1) :=
    continuous_fst.continuousAt.tendsto.comp convergence
  have coefficientConvergence : Tendsto (fun index => (sequence index).2) atTop (nhds limitPair.2) :=
    continuous_snd.continuousAt.tendsto.comp convergence
  have fixedLimit := (TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace_isClosed data level).mem_of_tendsto
    vectorConvergence (Eventually.of_forall (fun index => (membership index).1))
  refine ⟨fixedLimit, ?_⟩
  obtain ⟨bound, boundProperty⟩ := coefficientConvergence.norm.bddAbove_range
  let constant := max 0 bound
  have coefficientLimits (order : ℕ) :
      Tendsto (fun index => weightedSeries data radius (sequence index).2 order) atTop
        (nhds (weightedSeries data radius limitPair.2 order)) :=
    (weightedCoefficient data radius order).continuous.continuousAt.tendsto.comp coefficientConvergence
  have coefficientBounds (index order : ℕ) :
      ‖weightedSeries data radius (sequence index).2 order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order :=
    (weightedSeries_norm_bound data radius (sequence index).2 order).trans
      (mul_le_mul_of_nonneg_right ((boundProperty (Set.mem_range_self index)).trans (le_max_right _ _))
        (pow_nonneg (inv_nonneg.mpr radius.property) order))
  exact realOrbit_powerSeries_limit data (fun index => (sequence index).1) limitPair.1 vectorConvergence
    (fun index => weightedSeries data radius (sequence index).2) (weightedSeries data radius limitPair.2)
    (radius / 2) (div_pos positiveRadius (by norm_num)) constant (radius : ℝ)⁻¹ (le_max_left _ _)
    (inv_nonneg.mpr radius.property) (halfRadius_bound radius positiveRadius)
    (fun index => (membership index).2) coefficientLimits coefficientBounds

noncomputable instance coefficientSpaceComplete (data : CuspidalRepresentation) :
    CompleteSpace (CoefficientSpace data) := by
  exact @lp.completeSpace ℕ
    (fun order => ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H) ⊤
    (fun order => binaryMultilinearNorm (order := order) (Target := data.H)) ⟨le_top⟩
    (binaryMultilinearComplete data)

noncomputable instance analyticStageComplete (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (radius : ℝ≥0) (positiveRadius : 0 < radius) :
    CompleteSpace (analyticStage data level radius positiveRadius) := by
  let _ : IsClosed (analyticStage data level radius positiveRadius : Set (data.H × CoefficientSpace data)) :=
    analyticStage_isClosed data level radius positiveRadius
  exact IsClosed.completeSpace_coe

noncomputable def stageHilbertMap (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (radius : ℝ≥0) (positiveRadius : 0 < radius) :
    analyticStage data level radius positiveRadius →L[ℂ] data.H :=
  (ContinuousLinearMap.fst ℂ data.H (CoefficientSpace data)).comp
    (analyticStage data level radius positiveRadius).subtypeL

theorem stageHilbertMap_mem_smooth (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (element : analyticStage data level radius positiveRadius) :
    stageHilbertMap data level radius positiveRadius element ∈ data.smooth := by
  exact (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.fixed_mem_smooth_iff_analyticAt_one data level openness compactness
    element.val.1 element.property.1).mpr element.property.2.hasFPowerSeriesAt.analyticAt

noncomputable def stageSmoothMap (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (radius : ℝ≥0) (positiveRadius : 0 < radius) :
    analyticStage data level radius positiveRadius →ₗ[ℂ] TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedSmooth data level where
  toFun element := ⟨⟨stageHilbertMap data level radius positiveRadius element,
    stageHilbertMap_mem_smooth data level openness compactness radius positiveRadius element⟩, element.property.1⟩
  map_add' first second := Subtype.ext (Subtype.ext (map_add (stageHilbertMap data level radius positiveRadius) first second))
  map_smul' scalar element := Subtype.ext (Subtype.ext (map_smul (stageHilbertMap data level radius positiveRadius) scalar element))

theorem mem_smooth_iff_exists_stage (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.H) (fixed : vector ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level) :
    vector ∈ data.smooth ↔ ∃ radius : ℝ≥0, ∃ positiveRadius : 0 < radius,
      ∃ element : analyticStage data level radius positiveRadius,
        stageHilbertMap data level radius positiveRadius element = vector := by
  constructor
  · intro smoothVector
    obtain ⟨series, expansionRadius, expansion⟩ :=
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.smooth_orbit_contDiffAt_one data ⟨vector, smoothVector⟩).analyticAt
    obtain ⟨radius, positiveRadius, radiusBound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp expansion.r_pos
    have radiusPositive : (0 : ℝ≥0) < radius := by exact_mod_cast positiveRadius
    have radiusRealPositive : (0 : ℝ) < radius := by exact_mod_cast radiusPositive
    obtain ⟨constant, _, coefficientBound⟩ := series.norm_mul_pow_le_of_lt_radius (radiusBound.trans_le expansion.r_le)
    let coefficients : CoefficientSpace data := ⟨fun order => (radius : ℝ) ^ order • series order,
      memℓp_infty (by
        refine ⟨constant, ?_⟩
        rintro value ⟨order, rfl⟩
        calc
          _ = ((radius : ℝ) ^ order) * ‖series order‖ :=
            (norm_smul _ _).trans (congrArg (fun value : ℝ => value * ‖series order‖)
              (Real.norm_of_nonneg (pow_nonneg radius.property order)))
          _ = ‖series order‖ * (radius : ℝ) ^ order := mul_comm _ _
          _ ≤ constant := coefficientBound order)⟩
    have recoverSeries : weightedSeries data radius coefficients = series := by
      funext order
      change ((radius : ℝ)⁻¹ ^ order) • ((radius : ℝ) ^ order • series order) = series order
      calc
        _ = (((radius : ℝ)⁻¹ ^ order) * (radius : ℝ) ^ order) • series order := smul_smul _ _ _
        _ = series order := by rw [← mul_pow, inv_mul_cancel₀ radiusRealPositive.ne', one_pow, one_smul]
    have halfLe : ((radius / 2 : ℝ≥0) : ENNReal) ≤ (radius : ENNReal) := by
      exact_mod_cast (div_le_self (show (0 : ℝ≥0) ≤ radius from zero_le) (show (1 : ℝ≥0) ≤ 2 by norm_num))
    have pairMembership : (vector, coefficients) ∈ analyticStage data level radius radiusPositive := by
      refine ⟨fixed, ?_⟩
      change HasFPowerSeriesOnBall (realOrbit data vector) (weightedSeries data radius coefficients) 1 _
      rw [recoverSeries]
      exact expansion.mono (halfRadius_pos radius radiusPositive) (halfLe.trans radiusBound.le)
    exact ⟨radius, radiusPositive, ⟨(vector, coefficients), pairMembership⟩, rfl⟩
  · rintro ⟨radius, positiveRadius, element, equality⟩
    exact equality ▸ stageHilbertMap_mem_smooth data level openness compactness radius positiveRadius element

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
