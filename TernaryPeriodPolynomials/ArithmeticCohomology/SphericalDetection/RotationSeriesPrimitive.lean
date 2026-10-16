module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.DiskTaylorWeights

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def rotationSeriesMultiplier (weight : ℤ) (target index : ℕ) : ℂ :=
  (rotationSeparationPhase ^ (weight - 2 * (index : ℤ)) -
    rotationSeparationPhase ^ (weight - 2 * (target : ℤ)))⁻¹

theorem rotationSeriesMultiplier_self (weight : ℤ) (target : ℕ) :
    rotationSeriesMultiplier weight target target = 0 := by
  simp [rotationSeriesMultiplier]

theorem rotationSeriesMultiplier_bound (weight : ℤ) (target index : ℕ) :
    ‖rotationSeriesMultiplier weight target index‖ ≤ (25 : ℝ) ^ (index + target) := by
  by_cases same : index = target
  · subst index
    rw [rotationSeriesMultiplier_self, norm_zero]
    positivity
  have distinct : weight - 2 * (index : ℤ) ≠ weight - 2 * (target : ℤ) := by omega
  have bound := rotationSeparationPhase_sub_inv_bound _ _ distinct
  have exponent : ((weight - 2 * (index : ℤ)) - (weight - 2 * (target : ℤ))).natAbs ≤
      2 * (index + target) := by
    have difference : (weight - 2 * (index : ℤ)) - (weight - 2 * (target : ℤ)) =
        2 * ((target : ℤ) - index) := by ring
    rw [difference, Int.natAbs_mul]
    change 2 * ((target : ℤ) - index).natAbs ≤ 2 * (index + target)
    have triangle := Int.natAbs_sub_le (target : ℤ) (index : ℤ)
    simpa only [Int.natAbs_natCast, Nat.add_comm] using Nat.mul_le_mul_left 2 triangle
  calc
    _ ≤ (5 : ℝ) ^ ((weight - 2 * (index : ℤ)) - (weight - 2 * (target : ℤ))).natAbs := bound
    _ ≤ (5 : ℝ) ^ (2 * (index + target)) := pow_le_pow_right₀ (by norm_num) exponent
    _ = _ := by rw [pow_mul]; norm_num

def rotationSeriesPrimitive {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (weight : ℤ) (target : ℕ) (coefficients : ℕ → E) (point : ℂ) : E :=
  ∑' index, point ^ index • (rotationSeriesMultiplier weight target index • coefficients index)

theorem rotationSeriesPrimitive_summable
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (weight : ℤ) (target : ℕ) (coefficients : ℕ → E) (point : ℂ)
    (radius constant : ℝ) (radius_positive : 0 < radius) (_constant_nonnegative : 0 ≤ constant)
    (bound : ∀ index, ‖coefficients index‖ ≤ constant / radius ^ index)
    (inside : 25 * ‖point‖ < radius) :
    Summable (fun index => point ^ index •
      (rotationSeriesMultiplier weight target index • coefficients index)) := by
  have ratio_nonnegative : 0 ≤ 25 * ‖point‖ / radius := by positivity
  have ratio_small : 25 * ‖point‖ / radius < 1 := (div_lt_one radius_positive).mpr inside
  have geometric : Summable (fun index : ℕ => (25 * ‖point‖ / radius) ^ index) :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg ratio_nonnegative])
  apply (geometric.mul_left (constant * 25 ^ target)).of_norm_bounded
  intro index
  calc
    _ = ‖point‖ ^ index * ‖rotationSeriesMultiplier weight target index‖ * ‖coefficients index‖ := by
      rw [norm_smul, norm_smul, norm_pow, mul_assoc]
    _ ≤ ‖point‖ ^ index * (25 : ℝ) ^ (index + target) * (constant / radius ^ index) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (rotationSeriesMultiplier_bound weight target index) (by positivity)
      · exact bound index
      · exact norm_nonneg _
      · positivity
    _ = _ := by rw [pow_add, div_pow, mul_pow]; ring

theorem rotationSeriesPrimitive_equation
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (operator : E →L[ℂ] E) (weight : ℤ) (target : ℕ)
    (coefficients : ℕ → E) (point : ℂ) (value : E)
    (eigenvectors : ∀ index, operator (coefficients index) =
      rotationSeparationPhase ^ (weight - 2 * (index : ℤ)) • coefficients index)
    (expansion : HasSum (fun index => point ^ index • coefficients index) value)
    (converges : Summable (fun index => point ^ index •
      (rotationSeriesMultiplier weight target index • coefficients index))) :
    operator (rotationSeriesPrimitive weight target coefficients point) -
      rotationSeparationPhase ^ (weight - 2 * (target : ℤ)) •
        rotationSeriesPrimitive weight target coefficients point =
      value - point ^ target • coefficients target := by
  classical
  have transformed := (operator.hasSum converges.hasSum).sub
    (converges.hasSum.const_smul (rotationSeparationPhase ^ (weight - 2 * (target : ℤ))))
  have removed := expansion.sub (hasSum_ite_eq target (point ^ target • coefficients target))
  apply HasSum.unique transformed
  apply removed.congr_fun
  intro index
  by_cases same : index = target
  · subst index
    simp only [rotationSeriesMultiplier_self, zero_smul, smul_zero, map_zero, sub_self, ite_true]
  · rw [ite_eq_right same, sub_zero, map_smul, map_smul, eigenvectors]
    have distinct : rotationSeparationPhase ^ (weight - 2 * (index : ℤ)) ≠
        rotationSeparationPhase ^ (weight - 2 * (target : ℤ)) := by
      intro equality
      have exponents := rotationSeparationPhase_zpow_injective equality
      omega
    simp only [smul_smul]
    rw [← sub_smul]
    congr 1
    unfold rotationSeriesMultiplier
    field_simp

theorem powerSeries_coeff_geometric_bound
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {function : ℂ → E} {series : FormalMultilinearSeries ℂ ℂ E}
    (expansion : HasFPowerSeriesAt function series 0) :
    ∃ radius constant : ℝ, 0 < radius ∧ 0 < constant ∧
      ∀ index, ‖series.coeff index‖ ≤ constant / radius ^ index := by
  obtain ⟨radius, radius_positive, radius_small⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp expansion.radius_pos
  have positive : 0 < radius := by exact_mod_cast radius_positive
  obtain ⟨constant, constant_positive, bound⟩ :=
    series.norm_le_div_pow_of_pos_of_lt_radius positive radius_small
  refine ⟨radius, constant, positive, constant_positive, ?_⟩
  intro index
  calc
    ‖series.coeff index‖ ≤ ‖series index‖ := by
      change ‖(series index) (fun _ => (1 : ℂ))‖ ≤ ‖series index‖
      simpa only [norm_one, Finset.prod_const_one, mul_one]
        using (series index).le_opNorm (fun _ => (1 : ℂ))
    _ ≤ _ := bound index

theorem cuspDiskTaylorSeries_primitive (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (2 * halfWeight) • vector)
    (series : FormalMultilinearSeries ℂ ℂ cusp.H)
    (expansion : HasFPowerSeriesAt (cuspDiskOrbit cusp halfWeight vector) series 0)
    (target : ℕ) :
    ∀ᶠ point : ℂ in nhds 0,
      cusp.π (atInfinity (binaryRotations rotationSeparatingCircle))
          (rotationSeriesPrimitive (2 * halfWeight) target series.coeff point) -
        rotationSeparationPhase ^ (2 * halfWeight - 2 * (target : ℤ)) •
          rotationSeriesPrimitive (2 * halfWeight) target series.coeff point =
        cuspDiskOrbit cusp halfWeight vector point - point ^ target • series.coeff target := by
  obtain ⟨radius, constant, positive, constant_positive, bound⟩ :=
    powerSeries_coeff_geometric_bound expansion
  have neighborhood : ∀ᶠ point : ℂ in nhds 0, 25 * ‖point‖ < radius := by
    apply (isOpen_lt (continuous_const.mul continuous_norm) continuous_const).mem_nhds
    simpa using positive
  filter_upwards [neighborhood, hasFPowerSeriesAt_iff.mp expansion] with point inside summation
  exact rotationSeriesPrimitive_equation
    (cuspUnitaryOperator cusp (atInfinity (binaryRotations rotationSeparatingCircle)))
    (2 * halfWeight) target series.coeff point (cuspDiskOrbit cusp halfWeight vector point)
    (fun index => cuspDiskTaylorSeries_weight cusp halfWeight vector rotation series expansion index
      rotationSeparatingCircle)
    (by simpa only [zero_add] using summation)
    (rotationSeriesPrimitive_summable (2 * halfWeight) target series.coeff point
      radius constant positive constant_positive.le bound inside)

theorem rotationSeriesPrimitive_spherical (cusp : CuspidalRepresentation) (weight : ℤ) (target : ℕ)
    (coefficients : ℕ → cusp.H) (spherical : ∀ index, coefficients index ∈ cuspSphericalValues cusp)
    (point : ℂ) : rotationSeriesPrimitive weight target coefficients point ∈ cuspSphericalValues cusp := by
  unfold rotationSeriesPrimitive
  by_cases converges : Summable (fun index => point ^ index •
      (rotationSeriesMultiplier weight target index • coefficients index))
  · apply (cuspSphericalValues_closed cusp).mem_of_tendsto converges.hasSum
    filter_upwards [] with indices
    exact (cuspSphericalValues cusp).sum_mem (fun index _ =>
      (cuspSphericalValues cusp).smul_mem _ ((cuspSphericalValues cusp).smul_mem _ (spherical index)))
  · rw [tsum_eq_zero_of_not_summable converges]
    exact (cuspSphericalValues cusp).zero_mem



end TernaryPeriodPolynomials.SphericalDetection.Helpers
