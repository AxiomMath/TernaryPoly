module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Orbit
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation
open scoped Matrix.Norms.Elementwise NNReal
open Filter

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticLimits

noncomputable instance binaryMultilinearComplete (data : CuspidalRepresentation) (order : ℕ) :
    CompleteSpace (ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H) := by
  let _ : SequentialSpace (Fin order → BinaryMatrix) :=
    inferInstanceAs (SequentialSpace (Fin order → Fin 2 → Fin 2 → ℝ))
  exact ContinuousMultilinearMap.instCompleteSpace

theorem powerSeries_limit {Domain Target : Type}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target]
    (functions : ℕ → Domain → Target) (limitFunction : Domain → Target)
    (series : ℕ → FormalMultilinearSeries ℝ Domain Target)
    (limitSeries : FormalMultilinearSeries ℝ Domain Target)
    (center : Domain) (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (constant rate : ℝ) (nonnegativeConstant : 0 ≤ constant) (nonnegativeRate : 0 ≤ rate)
    (radiusBound : rate * (radius : ℝ) < 1)
    (expansions : ∀ index, HasFPowerSeriesOnBall (functions index) (series index) center radius)
    (coefficientLimits : ∀ order, Tendsto (fun index => series index order) atTop (nhds (limitSeries order)))
    (coefficientBounds : ∀ index order, ‖series index order‖ ≤ constant * rate ^ order)
    (functionLimits : ∀ point ∈ Metric.eball center (radius : ENNReal),
      Tendsto (fun index => functions index point) atTop (nhds (limitFunction point))) :
    HasFPowerSeriesOnBall limitFunction limitSeries center radius := by
  have limitBounds (order : ℕ) : ‖limitSeries order‖ ≤ constant * rate ^ order :=
    le_of_tendsto (coefficientLimits order).norm (Eventually.of_forall (fun index => coefficientBounds index order))
  have radiusLe : (radius : ENNReal) ≤ limitSeries.radius := by
    apply limitSeries.le_radius_of_bound constant
    intro order
    calc
      ‖limitSeries order‖ * (radius : ℝ) ^ order ≤
          (constant * rate ^ order) * (radius : ℝ) ^ order :=
        mul_le_mul_of_nonneg_right (limitBounds order) (pow_nonneg radius.property order)
      _ = constant * (rate * (radius : ℝ)) ^ order := by rw [mul_pow, mul_assoc]
      _ ≤ constant := mul_le_of_le_one_right nonnegativeConstant
        (pow_le_one₀ (mul_nonneg nonnegativeRate radius.property) radiusBound.le)
  refine ⟨radiusLe, by exact_mod_cast positiveRadius, ?_⟩
  intro offset membership
  have offsetBound : ‖offset‖ < (radius : ℝ) := by
    have bound : ‖offset‖₊ < radius := by
      simpa only [Metric.mem_eball, edist_lt_coe, nndist_zero_right] using membership
    exact_mod_cast bound
  have ratioNonnegative : 0 ≤ rate * ‖offset‖ := mul_nonneg nonnegativeRate (norm_nonneg _)
  have ratioBound : rate * ‖offset‖ < 1 :=
    (mul_le_mul_of_nonneg_left offsetBound.le nonnegativeRate).trans_lt radiusBound
  have summableBound : Summable (fun order : ℕ => constant * (rate * ‖offset‖) ^ order) :=
    (summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg ratioNonnegative])).mul_left constant
  have evaluationBound (coefficient : FormalMultilinearSeries ℝ Domain Target)
      (bound : ∀ order, ‖coefficient order‖ ≤ constant * rate ^ order) (order : ℕ) :
      ‖coefficient order (fun _ => offset)‖ ≤ constant * (rate * ‖offset‖) ^ order := by
    calc
      _ ≤ ‖coefficient order‖ * ∏ _ : Fin order, ‖offset‖ := (coefficient order).le_opNorm _
      _ = ‖coefficient order‖ * ‖offset‖ ^ order := by simp
      _ ≤ (constant * rate ^ order) * ‖offset‖ ^ order :=
        mul_le_mul_of_nonneg_right (bound order) (pow_nonneg (norm_nonneg _) order)
      _ = constant * (rate * ‖offset‖) ^ order := by rw [mul_pow, mul_assoc]
  have evaluationLimits (order : ℕ) :
      Tendsto (fun index => series index order (fun _ => offset)) atTop
        (nhds (limitSeries order (fun _ => offset))) :=
    (coefficientLimits order).eval_const (fun _ => offset)
  have sumLimits := tendsto_tsum_of_dominated_convergence summableBound evaluationLimits
    (Eventually.of_forall (fun index order => evaluationBound (series index) (coefficientBounds index) order))
  have shiftedMembership : center + offset ∈ Metric.eball center (radius : ENNReal) := by
    have distanceEquality : edist (center + offset) center = edist offset 0 := by
      simpa only [add_zero] using edist_add_left center offset (0 : Domain)
    simpa only [Metric.mem_eball, distanceEquality] using membership
  have sumsEqual : (fun index => ∑' order, series index order (fun _ => offset)) =
      (fun index => functions index (center + offset)) := by
    funext index
    exact ((expansions index).hasSum membership).tsum_eq
  rw [sumsEqual] at sumLimits
  have sumEquality := tendsto_nhds_unique sumLimits (functionLimits _ shiftedMembership)
  exact sumEquality ▸ (summableBound.of_norm_bounded (evaluationBound limitSeries limitBounds)).hasSum

theorem realOrbit_powerSeries_limit (data : CuspidalRepresentation)
    (vectors : ℕ → data.H) (limitVector : data.H)
    (vectorLimit : Tendsto vectors atTop (nhds limitVector))
    (series : ℕ → FormalMultilinearSeries ℝ BinaryMatrix data.H)
    (limitSeries : FormalMultilinearSeries ℝ BinaryMatrix data.H)
    (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (constant rate : ℝ) (nonnegativeConstant : 0 ≤ constant) (nonnegativeRate : 0 ≤ rate)
    (radiusBound : rate * (radius : ℝ) < 1)
    (expansions : ∀ index, HasFPowerSeriesOnBall (realOrbit data (vectors index)) (series index) 1 radius)
    (coefficientLimits : ∀ order, Tendsto (fun index => series index order) atTop (nhds (limitSeries order)))
    (coefficientBounds : ∀ index order, ‖series index order‖ ≤ constant * rate ^ order) :
    HasFPowerSeriesOnBall (realOrbit data limitVector) limitSeries 1 radius := by
  apply powerSeries_limit (fun index => realOrbit data (vectors index)) (realOrbit data limitVector)
    series limitSeries 1 radius positiveRadius constant rate nonnegativeConstant nonnegativeRate
    radiusBound expansions coefficientLimits coefficientBounds
  intro matrix _
  exact (TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.unitaryOperator data (atInfinity (invertibleMatrix matrix))).continuous.continuousAt.tendsto.comp
    vectorLimit

/-- A common convergent power-series bound preserves the actual analytic-vector condition. -/
theorem fixed_limit_mem_smooth (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vectors : ℕ → data.H) (fixed : ∀ index, vectors index ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level)
    (limitVector : data.H) (vectorLimit : Tendsto vectors atTop (nhds limitVector))
    (series : ℕ → FormalMultilinearSeries ℝ BinaryMatrix data.H)
    (limitSeries : FormalMultilinearSeries ℝ BinaryMatrix data.H)
    (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (constant rate : ℝ) (nonnegativeConstant : 0 ≤ constant) (nonnegativeRate : 0 ≤ rate)
    (radiusBound : rate * (radius : ℝ) < 1)
    (expansions : ∀ index, HasFPowerSeriesOnBall (realOrbit data (vectors index)) (series index) 1 radius)
    (coefficientLimits : ∀ order, Tendsto (fun index => series index order) atTop (nhds (limitSeries order)))
    (coefficientBounds : ∀ index order, ‖series index order‖ ≤ constant * rate ^ order) :
    limitVector ∈ data.smooth ∧ limitVector ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level := by
  have fixedLimit := (TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace_isClosed data level).mem_of_tendsto
    vectorLimit (Eventually.of_forall fixed)
  refine ⟨?_, fixedLimit⟩
  apply (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.fixed_mem_smooth_iff_analyticAt_one data level openness compactness
    limitVector fixedLimit).mpr
  exact (realOrbit_powerSeries_limit data vectors limitVector vectorLimit series limitSeries radius
    positiveRadius constant rate nonnegativeConstant nonnegativeRate radiusBound expansions
    coefficientLimits coefficientBounds).hasFPowerSeriesAt.analyticAt

/-- Coefficient Cauchy sequences with a common analytic bound have a supplied smooth-vector limit. -/
theorem exists_fixed_smooth_limit (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vectors : ℕ → data.H) (fixed : ∀ index, vectors index ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level)
    (series : ℕ → FormalMultilinearSeries ℝ BinaryMatrix data.H)
    (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (constant rate : ℝ) (nonnegativeConstant : 0 ≤ constant) (nonnegativeRate : 0 ≤ rate)
    (radiusBound : rate * (radius : ℝ) < 1)
    (expansions : ∀ index, HasFPowerSeriesOnBall (realOrbit data (vectors index)) (series index) 1 radius)
    (coefficientCauchy : ∀ order, CauchySeq (fun index => series index order))
    (coefficientBounds : ∀ index order, ‖series index order‖ ≤ constant * rate ^ order) :
    ∃ limitVector : TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedSmooth data level,
      Tendsto vectors atTop (nhds limitVector.val.val) ∧
      ∃ limitSeries : FormalMultilinearSeries ℝ BinaryMatrix data.H,
        (∀ order, Tendsto (fun index => series index order) atTop (nhds (limitSeries order))) ∧
        HasFPowerSeriesOnBall (realOrbit data limitVector.val.val) limitSeries 1 radius := by
  have coefficientExistence (order : ℕ) := cauchySeq_tendsto_of_complete (coefficientCauchy order)
  choose limitSeries coefficientLimits using coefficientExistence
  let limitVector : data.H := limitSeries 0 (0 : Fin 0 → BinaryMatrix)
  have coefficientZero (index : ℕ) : series index 0 (0 : Fin 0 → BinaryMatrix) = vectors index := by
    exact ((expansions index).coeff_zero (0 : Fin 0 → BinaryMatrix)).trans
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.realOrbit_one data (vectors index))
  have vectorLimit : Tendsto vectors atTop (nhds limitVector) := by
    simpa only [coefficientZero] using (coefficientLimits 0).eval_const (0 : Fin 0 → BinaryMatrix)
  have limitMembership := fixed_limit_mem_smooth data level openness compactness vectors fixed
    limitVector vectorLimit series limitSeries radius positiveRadius constant rate nonnegativeConstant
    nonnegativeRate radiusBound expansions coefficientLimits coefficientBounds
  refine ⟨⟨⟨limitVector, limitMembership.1⟩, limitMembership.2⟩, vectorLimit,
    limitSeries, coefficientLimits, ?_⟩
  exact realOrbit_powerSeries_limit data vectors limitVector vectorLimit series limitSeries radius
    positiveRadius constant rate nonnegativeConstant nonnegativeRate radiusBound expansions
    coefficientLimits coefficientBounds

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticLimits
