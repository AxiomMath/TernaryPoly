module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.DiskFourierCoefficients

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance rotationKernelMeasurable : MeasurableSpace Circle := borel Circle
local instance rotationKernelBorel : BorelSpace Circle := ⟨rfl⟩

def rotationSeriesKernelTerm (weight : ℤ) (target : ℕ) (point : ℂ) (radius : NNReal)
    (index : ℕ) (angle : Circle) : ℂ :=
  ((point / (radius : ℂ)) ^ index * rotationSeriesMultiplier weight target index) *
    (angle : ℂ) ^ (-(index : ℤ))

def rotationSeriesKernel (weight : ℤ) (target : ℕ) (point : ℂ) (radius : NNReal) (angle : Circle) : ℂ :=
  ∑' index, rotationSeriesKernelTerm weight target point radius index angle

theorem rotationSeriesKernelTerm_continuous (weight : ℤ) (target : ℕ) (point : ℂ)
    (radius : NNReal) (index : ℕ) : Continuous (rotationSeriesKernelTerm weight target point radius index) :=
  continuous_const.mul (circleCharacter_continuous _)

theorem rotationSeriesKernelTerm_bound (weight : ℤ) (target : ℕ) (point : ℂ)
    (radius : NNReal) (index : ℕ) (angle : Circle) :
    ‖rotationSeriesKernelTerm weight target point radius index angle‖ ≤
      (25 : ℝ) ^ target * (25 * ‖point‖ / radius) ^ index := by
  simp only [rotationSeriesKernelTerm, norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one,
    norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg radius.coe_nonneg]
  calc
    _ ≤ (‖point‖ / radius) ^ index * (25 : ℝ) ^ (index + target) :=
      mul_le_mul_of_nonneg_left (rotationSeriesMultiplier_bound weight target index) (by positivity)
    _ = _ := by simp only [pow_add, div_pow, mul_pow]; ring

theorem rotationSeriesKernel_bound_summable (target : ℕ) (point : ℂ) (radius : NNReal)
    (positive : 0 < radius) (inside : 25 * ‖point‖ < radius) :
    Summable (fun index : ℕ => (25 : ℝ) ^ target * (25 * ‖point‖ / radius) ^ index) := by
  have nonnegative : 0 ≤ 25 * ‖point‖ / radius := by positivity
  have small : 25 * ‖point‖ / radius < 1 := (div_lt_one (show (0 : ℝ) < radius from positive)).mpr inside
  have geometric : Summable (fun index : ℕ => (25 * ‖point‖ / (radius : ℝ)) ^ index) :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg nonnegative])
  exact geometric.mul_left ((25 : ℝ) ^ target)

theorem rotationSeriesKernel_continuous (weight : ℤ) (target : ℕ) (point : ℂ) (radius : NNReal)
    (positive : 0 < radius) (inside : 25 * ‖point‖ < radius) :
    Continuous (rotationSeriesKernel weight target point radius) :=
  continuous_tsum (rotationSeriesKernelTerm_continuous weight target point radius)
    (rotationSeriesKernel_bound_summable target point radius positive inside)
    (rotationSeriesKernelTerm_bound weight target point radius)

theorem rotationSeriesPrimitive_eq_integral
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (function : ℂ → E) (series : FormalMultilinearSeries ℂ ℂ E)
    (outerRadius : ENNReal) (expansion : HasFPowerSeriesOnBall function series 0 outerRadius)
    (radius : NNReal) (positive : 0 < radius) (radius_inside : (radius : ENNReal) < outerRadius)
    (weight : ℤ) (target : ℕ) (point : ℂ) (inside : 25 * ‖point‖ < radius) :
    rotationSeriesPrimitive weight target series.coeff point =
      ∫ angle : Circle, rotationSeriesKernel weight target point radius angle •
        function ((radius : ℂ) * (angle : ℂ)) ∂binaryRotationMeasure := by
  let orbit : Circle → E := fun angle => function ((radius : ℂ) * (angle : ℂ))
  have orbit_continuous : Continuous orbit := expansion.continuousOn.comp_continuous
    (continuous_const.mul (by fun_prop)) (by
      intro angle
      rw [Metric.mem_eball, edist_zero_right]
      have point_norm : ‖(radius : ℂ) * (angle : ℂ)‖₊ = radius := by
        apply NNReal.eq
        change ‖(radius : ℂ) * (angle : ℂ)‖ = (radius : ℝ)
        simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg radius.coe_nonneg]
      simpa only [enorm_eq_nnnorm, point_norm] using radius_inside)
  obtain ⟨constant, bound⟩ := isCompact_univ.exists_bound_of_continuousOn orbit_continuous.continuousOn
  let majorant : ℕ → ℝ := fun index => (25 : ℝ) ^ target * (25 * ‖point‖ / radius) ^ index
  have bound_summable : Summable majorant := rotationSeriesKernel_bound_summable target point radius positive inside
  have integrated := hasSum_integral_of_dominated_convergence (μ := binaryRotationMeasure)
    (fun index _ => majorant index * max constant 0)
    (fun index => ((rotationSeriesKernelTerm_continuous weight target point radius index).smul
      orbit_continuous).aestronglyMeasurable) (by
      intro index
      filter_upwards [] with angle
      change ‖rotationSeriesKernelTerm weight target point radius index angle • orbit angle‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul (rotationSeriesKernelTerm_bound weight target point radius index angle)
        ((bound angle (Set.mem_univ _)).trans (le_max_left _ _)) (norm_nonneg _) (by dsimp [majorant]; positivity))
    (Filter.Eventually.of_forall (fun _ => bound_summable.mul_right (max constant 0)))
    (integrable_const _) (by
      filter_upwards [] with angle
      exact ((bound_summable.of_norm_bounded (fun index =>
        rotationSeriesKernelTerm_bound weight target point radius index angle)).hasSum).smul_const (orbit angle))
  have integrated_term (index : ℕ) :
      (∫ angle, rotationSeriesKernelTerm weight target point radius index angle • orbit angle
        ∂binaryRotationMeasure) = point ^ index • (rotationSeriesMultiplier weight target index • series.coeff index) := by
    simp only [rotationSeriesKernelTerm, mul_smul]
    rw [integral_smul, integral_smul]
    change (point / (radius : ℂ)) ^ index • (rotationSeriesMultiplier weight target index •
      (∫ angle : Circle, (angle : ℂ) ^ (-(index : ℤ)) • function ((radius : ℂ) * (angle : ℂ))
        ∂binaryRotationMeasure)) = _
    rw [powerSeries_circle_coefficient function series outerRadius expansion radius radius_inside index]
    simp only [smul_smul, div_pow]
    congr 1
    have nonzero : (radius : ℂ) ^ index ≠ 0 := pow_ne_zero index (by exact_mod_cast ne_of_gt positive)
    field_simp
  change HasSum (fun index => ∫ angle, rotationSeriesKernelTerm weight target point radius index angle •
    orbit angle ∂binaryRotationMeasure) (∫ angle, rotationSeriesKernel weight target point radius angle •
      orbit angle ∂binaryRotationMeasure) at integrated
  simp only [integrated_term] at integrated
  exact integrated.tsum_eq

theorem cuspDiskTaylorSeries_primitive_smooth (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet)
    (series : FormalMultilinearSeries ℂ ℂ cusp.H)
    (expansion : HasFPowerSeriesAt (cuspDiskOrbit cusp halfWeight vector.val) series 0)
    (target : ℕ) :
    ∀ᶠ point : ℂ in nhds 0,
      rotationSeriesPrimitive (2 * halfWeight) target series.coeff point ∈ cusp.smooth := by
  obtain ⟨radius, positive, small, averaging⟩ :=
    cuspDiskOrbit_exists_smooth_average_radius cusp halfWeight vector spherical holomorphic
  obtain ⟨larger, larger_than, larger_small⟩ := exists_between small
  have larger_positive : 0 < larger := positive.trans larger_than
  have expansion_on_ball := cuspDiskTaylorSeries_onBall cusp halfWeight vector.val holomorphic
    series expansion larger larger_positive larger_small
  have neighborhood : ∀ᶠ point : ℂ in nhds 0, 25 * ‖point‖ < radius := by
    apply (isOpen_lt (continuous_const.mul continuous_norm) continuous_const).mem_nhds
    simpa using (show (0 : ℝ) < radius from positive)
  filter_upwards [neighborhood] with point inside
  rw [rotationSeriesPrimitive_eq_integral _ series larger expansion_on_ball radius positive
    (by exact_mod_cast larger_than) (2 * halfWeight) target point inside]
  exact averaging _ (rotationSeriesKernel_continuous _ _ _ _ positive inside)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
