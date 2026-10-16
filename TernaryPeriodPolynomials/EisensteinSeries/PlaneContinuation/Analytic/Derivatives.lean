module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Stages
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDerivatives

theorem powerSeries_iteratedFDeriv_norm_le {Domain Target : Type}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target]
    {function : Domain → Target} {series : FormalMultilinearSeries ℝ Domain Target}
    {center : Domain} {radius : ENNReal}
    (expansion : HasFPowerSeriesOnBall function series center radius) (order : ℕ) :
    ‖iteratedFDeriv ℝ order function center‖ ≤ (order.factorial : ℝ) * ‖series order‖ := by
  classical
  have equality : iteratedFDeriv ℝ order function center =
      ∑ permutation : Equiv.Perm (Fin order), ContinuousMultilinearMap.domDomCongr permutation (series order) := by
    apply ContinuousMultilinearMap.ext
    intro directions
    simpa only [sum_apply, ContinuousMultilinearMap.domDomCongr_apply] using
      expansion.iteratedFDeriv_eq_sum_of_completeSpace directions
  rw [equality]
  apply (norm_sum_le _ _).trans_eq
  simp only [ContinuousMultilinearMap.norm_domDomCongr, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem stage_orbitDerivative_bound (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (element : analyticStage data level radius positiveRadius) (order : ℕ) :
    ‖orbitDerivative data order element.val.1‖ ≤
      ((order.factorial : ℝ) * (radius : ℝ)⁻¹ ^ order) * ‖element‖ := by
  have derivativeBound := powerSeries_iteratedFDeriv_norm_le element.property.2 order
  have coefficientBound := weightedSeries_norm_bound data radius element.val.2 order
  have coefficientNorm : ‖element.val.2‖ ≤ ‖element‖ := norm_snd_le _
  calc
    _ ≤ (order.factorial : ℝ) * ‖weightedSeries data radius element.val.2 order‖ := derivativeBound
    _ ≤ (order.factorial : ℝ) * (‖element.val.2‖ * (radius : ℝ)⁻¹ ^ order) :=
      mul_le_mul_of_nonneg_left coefficientBound (Nat.cast_nonneg _)
    _ ≤ (order.factorial : ℝ) * (‖element‖ * (radius : ℝ)⁻¹ ^ order) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right coefficientNorm (pow_nonneg (inv_nonneg.mpr radius.property) order))
        (Nat.cast_nonneg _)
    _ = _ := by ring

theorem stage_orbitSobolevNorm_bound (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (element : analyticStage data level radius positiveRadius) (order : ℕ) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevBounds.orbitSobolevNorm data order element.val.1 ≤
      (∑ derivativeOrder ∈ Finset.range (order + 1),
        (derivativeOrder.factorial : ℝ) * (radius : ℝ)⁻¹ ^ derivativeOrder) * ‖element‖ := by
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevBounds.orbitSobolevNorm, Finset.sum_mul]
  exact Finset.sum_le_sum (fun derivativeOrder _ =>
    stage_orbitDerivative_bound data level radius positiveRadius element derivativeOrder)

theorem stageSmoothMap_continuous (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (radius : ℝ≥0) (positiveRadius : 0 < radius) :
    letI := TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedTopology data level
    Continuous (stageSmoothMap data level openness compactness radius positiveRadius) := by
  let _ := TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedTopology data level
  apply (TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedTopology_withSeminorms data level).continuous_normedSpace_dom
    (analyticStage data level radius positiveRadius) (stageSmoothMap data level openness compactness radius positiveRadius)
  intro order
  let constant : ℝ := ∑ derivativeOrder ∈ Finset.range (order + 1),
    (derivativeOrder.factorial : ℝ) * (radius : ℝ)⁻¹ ^ derivativeOrder
  have nonnegativeConstant : 0 ≤ constant := Finset.sum_nonneg (fun derivativeOrder _ =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.mpr radius.property) derivativeOrder))
  refine ⟨(⟨constant, nonnegativeConstant⟩ : ℝ≥0), ?_⟩
  intro element
  change TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedSeminorms data level order
    (stageSmoothMap data level openness compactness radius positiveRadius element) ≤ constant * ‖element‖
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedSeminorms_apply]
  exact stage_orbitSobolevNorm_bound data level radius positiveRadius element order

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDerivatives
