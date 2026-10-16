module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RotationSeriesPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DiskAverage

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance diskFourierMeasurable : MeasurableSpace Circle := borel Circle
local instance diskFourierBorel : BorelSpace Circle := ⟨rfl⟩

theorem circleCharacter_continuous (weight : ℤ) :
    Continuous (fun angle : Circle => (angle : ℂ) ^ weight) :=
  (show Continuous (fun angle : Circle => (angle : ℂ)) by fun_prop).zpow₀ weight
    (fun angle => Or.inl (Circle.coe_ne_zero angle))

theorem circleCharacter_integral (weight : ℤ) :
    (∫ angle : Circle, (angle : ℂ) ^ weight ∂binaryRotationMeasure) = if weight = 0 then 1 else 0 := by
  by_cases zero : weight = 0
  · subst weight
    simp only [zpow_zero, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul, ite_true]
  · rw [ite_eq_right zero]
    have translated := integral_mul_left_eq_self (μ := binaryRotationMeasure)
      (fun angle : Circle => (angle : ℂ) ^ weight) rotationSeparatingCircle
    simp only [Circle.coe_mul, rotationSeparatingCircle_coe, mul_zpow, integral_const_mul] at translated
    have annihilates : (rotationSeparationPhase ^ weight - 1) *
        (∫ angle : Circle, (angle : ℂ) ^ weight ∂binaryRotationMeasure) = 0 := by
      linear_combination translated
    exact (mul_eq_zero.mp annihilates).resolve_left
      (sub_ne_zero.mpr (rotationSeparationPhase_zpow_ne_one weight zero))

theorem powerSeries_circle_coefficient
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (function : ℂ → E) (series : FormalMultilinearSeries ℂ ℂ E)
    (outerRadius : ENNReal) (expansion : HasFPowerSeriesOnBall function series 0 outerRadius)
    (radius : NNReal) (inside : (radius : ENNReal) < outerRadius) (target : ℕ) :
    (∫ angle : Circle, (angle : ℂ) ^ (-(target : ℤ)) • function ((radius : ℂ) * (angle : ℂ))
      ∂binaryRotationMeasure) = (radius : ℂ) ^ target • series.coeff target := by
  classical
  let terms : ℕ → Circle → E := fun index angle =>
    ((radius : ℂ) ^ index * (angle : ℂ) ^ ((index : ℤ) - target)) • series.coeff index
  have terms_continuous (index : ℕ) : Continuous (terms index) :=
    (continuous_const.mul (circleCharacter_continuous ((index : ℤ) - target))).smul continuous_const
  have terms_bound (index : ℕ) (angle : Circle) :
      ‖terms index angle‖ ≤ ‖series index‖ * (radius : ℝ) ^ index := by
    have coefficient_bound : ‖series.coeff index‖ ≤ ‖series index‖ := by
      change ‖(series index) (fun _ => (1 : ℂ))‖ ≤ ‖series index‖
      simpa only [norm_one, Finset.prod_const_one, mul_one] using
        (series index).le_opNorm (fun _ => (1 : ℂ))
    simp only [terms, norm_smul, norm_mul, norm_pow, norm_zpow, Circle.norm_coe,
      one_zpow, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg radius.coe_nonneg]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left coefficient_bound
      (pow_nonneg radius.coe_nonneg index)
  have summable_bound := series.summable_norm_mul_pow (inside.trans_le expansion.r_le)
  have integrated := hasSum_integral_of_dominated_convergence (μ := binaryRotationMeasure)
    (fun index _ => ‖series index‖ * (radius : ℝ) ^ index)
    (fun index => (terms_continuous index).aestronglyMeasurable)
    (fun index => Filter.Eventually.of_forall (terms_bound index))
    (Filter.Eventually.of_forall (fun _ => summable_bound)) (integrable_const _) (by
      filter_upwards [] with angle
      have point_inside : (radius : ℂ) * (angle : ℂ) ∈ Metric.eball 0 outerRadius := by
        rw [Metric.mem_eball, edist_zero_right]
        have point_norm : ‖(radius : ℂ) * (angle : ℂ)‖₊ = radius := by
          apply NNReal.eq
          change ‖(radius : ℂ) * (angle : ℂ)‖ = (radius : ℝ)
          simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg radius.coe_nonneg]
        simpa only [enorm_eq_nnnorm, point_norm] using inside
      have sum := (expansion.hasSum point_inside).const_smul ((angle : ℂ) ^ (-(target : ℤ)))
      simp only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff] at sum
      apply sum.congr_fun
      intro index
      simp only [terms, smul_smul, ← zpow_natCast, mul_zpow]
      rw [sub_eq_add_neg, zpow_add₀ (Circle.coe_ne_zero angle)]
      congr 1
      ring)
  have integrated_term (index : ℕ) : (∫ angle, terms index angle ∂binaryRotationMeasure) =
      if index = target then (radius : ℂ) ^ target • series.coeff target else 0 := by
    simp only [terms, mul_smul]
    rw [integral_smul, integral_smul_const, circleCharacter_integral]
    by_cases same : index = target
    · subst index
      simp
    · have distinct : (index : ℤ) - target ≠ 0 := by omega
      simp only [ite_eq_right distinct, zero_smul, smul_zero, ite_eq_right same]
  simp only [integrated_term] at integrated
  exact integrated.unique (hasSum_ite_eq target ((radius : ℂ) ^ target • series.coeff target))

theorem cuspDiskTaylorSeries_onBall (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (series : FormalMultilinearSeries ℂ ℂ cusp.H)
    (expansion : HasFPowerSeriesAt (cuspDiskOrbit cusp halfWeight vector) series 0)
    (radius : NNReal) (positive : 0 < radius) (small : radius < 1) :
    HasFPowerSeriesOnBall (cuspDiskOrbit cusp halfWeight vector) series 0 radius := by
  have disk_holomorphic := cuspDiskOrbit_holomorphic cusp halfWeight vector holomorphic
  have closed_holomorphic : DifferentiableOn ℂ (cuspDiskOrbit cusp halfWeight vector)
      (Metric.closedBall (0 : ℂ) radius) := disk_holomorphic.mono (by
    intro point member
    rw [Metric.mem_ball, dist_zero_right]
    have bound : ‖point‖ ≤ (radius : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using member
    exact bound.trans_lt (show (radius : ℝ) < 1 from small))
  have cauchy := closed_holomorphic.hasFPowerSeriesOnBall positive
  have unique := expansion.eq_formalMultilinearSeries cauchy.hasFPowerSeriesAt
  rw [unique]
  exact cauchy

theorem cuspDiskTaylorSeries_smooth (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet)
    (series : FormalMultilinearSeries ℂ ℂ cusp.H)
    (expansion : HasFPowerSeriesAt (cuspDiskOrbit cusp halfWeight vector.val) series 0)
    (index : ℕ) : series.coeff index ∈ cusp.smooth := by
  obtain ⟨radius, positive, small, averaging⟩ :=
    cuspDiskOrbit_exists_smooth_average_radius cusp halfWeight vector spherical holomorphic
  obtain ⟨larger, larger_than, larger_small⟩ := exists_between small
  have larger_positive : 0 < larger := positive.trans larger_than
  have expansion_on_ball := cuspDiskTaylorSeries_onBall cusp halfWeight vector.val holomorphic
    series expansion larger larger_positive larger_small
  have coefficient_smooth := averaging (fun angle : Circle => (angle : ℂ) ^ (-(index : ℤ)))
    (circleCharacter_continuous _)
  rw [powerSeries_circle_coefficient _ series larger expansion_on_ball radius
    (by exact_mod_cast larger_than) index] at coefficient_smooth
  have nonzero : (radius : ℂ) ^ index ≠ 0 :=
    pow_ne_zero index (by exact_mod_cast ne_of_gt positive)
  have recovered := cusp.smooth.smul_mem ((radius : ℂ) ^ index)⁻¹ coefficient_smooth
  simpa only [smul_smul, inv_mul_cancel₀ nonzero, one_smul] using recovered

end TernaryPeriodPolynomials.SphericalDetection.Helpers
