module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.ThetaDecay
public import Mathlib.Analysis.MellinTransform

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDecay
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarThetaContinuity

theorem matrix_continuousOn (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (lower : ℝ) (positive : 0 < lower) :
    ContinuousOn (fun scale : ℝ => ∑' matrix : Rectangular ℚ,
      realTest (scale • realVector matrix) * finiteTest (finiteMatrix matrix)) (Set.Ici lower) := by
  obtain ⟨majorant, summableMajorant, nonnegative, bounded⟩ :=
    RectangularSchwartz.exists_uniform_majorant (tsupport finiteTest) finiteSupport realTest
      lower⁻¹ (inv_nonneg.mpr positive.le)
  obtain ⟨bound, finiteBound⟩ := finiteSupport.exists_bound_of_continuous finiteContinuous
  apply continuousOn_tsum (fun matrix =>
    ((realTest.continuous.comp (continuous_id.smul continuous_const)).mul continuous_const).continuousOn)
    (summableMajorant.mul_right (max bound 0))
  intro matrix scale membership
  change ‖realTest (scale • realVector matrix) * finiteTest (finiteMatrix matrix)‖ ≤ majorant matrix * max bound 0
  rw [norm_mul]
  by_cases vanishing : finiteTest (finiteMatrix matrix) = 0
  · rw [vanishing, norm_zero, mul_zero]
    exact mul_nonneg (nonnegative matrix) (le_max_right _ _)
  · have scalePositive : 0 < scale := positive.trans_le membership
    have inverseBound : ∀ vector : RealSpace, ‖vector‖ ≤ lower⁻¹ * ‖scale • vector‖ := by
      intro vector
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos scalePositive, ← mul_assoc]
      apply le_mul_of_one_le_left (norm_nonneg _)
      simpa only [inv_mul_cancel₀ positive.ne'] using
        mul_le_mul_of_nonneg_left membership (inv_nonneg.mpr positive.le)
    have realBound := bounded (scale • ContinuousLinearMap.id ℝ RealSpace) inverseBound matrix
      (subset_closure vanishing)
    exact mul_le_mul realBound ((finiteBound _).trans (le_max_left _ _)) (norm_nonneg _) (nonnegative matrix)

theorem continuousOn (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) :
    ContinuousOn (theta realTest finiteTest) (Set.Ioi 0) := by
  intro scale positive
  have continuity := matrix_continuousOn realTest (finiteTest ∘ coordinateHomeomorph)
    (finiteContinuous.comp coordinateHomeomorph.continuous) (finiteSupport.comp_homeomorph coordinateHomeomorph)
    (scale / 2) (half_pos positive)
  simp only [Function.comp_apply, matrix_sum] at continuity
  exact (continuity.continuousAt (Ici_mem_nhds (half_lt_self positive))).continuousWithinAt

theorem locallyIntegrableOn (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) :
    LocallyIntegrableOn (theta realTest finiteTest) (Set.Ioi 0) :=
  (continuousOn realTest finiteTest finiteContinuous finiteSupport).locallyIntegrableOn measurableSet_Ioi

theorem decay_nat (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (order : ℕ) :
    (fun scale => theta realTest finiteTest scale - realTest 0 * finiteTest 0) =O[atTop]
      (fun scale : ℝ => scale ^ (-(order : ℝ))) := by
  obtain ⟨constant, _, bounded⟩ := rapid_large realTest finiteTest finiteContinuous finiteSupport order
  refine isBigO_iff.mpr ⟨constant, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with scale scaleLower
  have positive : 0 < scale := lt_of_lt_of_le zero_lt_one scaleLower
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg positive.le _),
    Real.rpow_neg positive.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos positive order)).mpr (by simpa only [mul_comm] using bounded scale scaleLower)

theorem decay (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (exponent : ℝ) :
    (fun scale => theta realTest finiteTest scale - realTest 0 * finiteTest 0) =O[atTop]
      (fun scale : ℝ => scale ^ exponent) := by
  obtain ⟨order, greater⟩ := exists_nat_gt (-exponent)
  apply (decay_nat realTest finiteTest finiteContinuous finiteSupport order).trans
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with scale scaleLower
  have nonnegative : 0 ≤ scale := zero_le_one.trans scaleLower
  simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg nonnegative _)] using
    Real.rpow_le_rpow_of_exponent_le scaleLower (by linarith : -(order : ℝ) ≤ exponent)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarThetaContinuity
