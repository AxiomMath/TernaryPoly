module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.LatticeBoundaryBounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section


open MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem rpow_tail_indicator_integral (threshold radius displacement : ℝ)
    (threshold_positive : 0 < threshold) (radius_large : threshold ≤ radius)
    (displacement_positive : 0 < displacement) :
    (∫ value : ℝ in Set.Ioi threshold,
      (Set.Ioi radius).indicator (fun value => value ^ (-4 - displacement)) value) =
        radius ^ (-3 - displacement) / (3 + displacement) := by
  rw [setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi radius_large),
    integral_Ioi_rpow_of_lt (by linarith) (threshold_positive.trans_le radius_large)]
  have exponent : -4 - displacement + 1 = -3 - displacement := by ring
  rw [exponent, show -3 - displacement = -(3 + displacement) by ring]
  rw [neg_div_neg_eq]

theorem finite_power_sum_of_count_bound {Index : Type*} [DecidableEq Index]
    (radius : Index → ℝ) (indices : Finset Index) (threshold coefficient displacement : ℝ)
    (threshold_positive : 0 < threshold) (displacement_positive : 0 < displacement)
    (radius_large : ∀ index ∈ indices, threshold ≤ radius index)
    (count_bound : ∀ value : ℝ, threshold < value →
      ((indices.filter (fun index => radius index < value)).card : ℝ) ≤ coefficient * value ^ 3) :
    (∑ index ∈ indices, (radius index) ^ (-3 - displacement)) ≤
      (3 + displacement) * coefficient * threshold ^ (-displacement) / displacement := by
  let kernel (index : Index) (value : ℝ) :=
    (Set.Ioi (radius index)).indicator (fun value => value ^ (-4 - displacement)) value
  have kernel_integrable (index : Index) : IntegrableOn (kernel index) (Set.Ioi threshold) volume :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -4 - displacement < -1) threshold_positive).indicator measurableSet_Ioi
  have sum_integrable : IntegrableOn (fun value => ∑ index ∈ indices, kernel index value) (Set.Ioi threshold) volume :=
    integrable_finsetSum indices (fun index _ => kernel_integrable index)
  have majorant_integrable : IntegrableOn (fun value : ℝ => coefficient * value ^ (-1 - displacement))
      (Set.Ioi threshold) volume :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - displacement < -1) threshold_positive).const_mul coefficient
  have bound_integral : (∫ value : ℝ in Set.Ioi threshold, ∑ index ∈ indices, kernel index value) ≤
      ∫ value : ℝ in Set.Ioi threshold, coefficient * value ^ (-1 - displacement) := by
    apply integral_mono_ae sum_integrable majorant_integrable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with value value_large
    change threshold < value at value_large
    have value_positive : 0 < value := threshold_positive.trans value_large
    have kernel_sum : (∑ index ∈ indices, kernel index value) =
        ((indices.filter (fun index => radius index < value)).card : ℝ) * value ^ (-4 - displacement) := by
      simp only [kernel, Set.indicator_apply, Set.mem_Ioi]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
    rw [kernel_sum]
    calc
      _ ≤ (coefficient * value ^ 3) * value ^ (-4 - displacement) :=
        mul_le_mul_of_nonneg_right (count_bound value value_large) (Real.rpow_nonneg value_positive.le _)
      _ = coefficient * value ^ (-1 - displacement) := by
        rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add value_positive]
        congr 2
        norm_num
        ring
  have sum_identity : (∑ index ∈ indices, (radius index) ^ (-3 - displacement)) =
      (3 + displacement) * ∫ value : ℝ in Set.Ioi threshold, ∑ index ∈ indices, kernel index value := by
    rw [integral_finsetSum indices (fun index _ => kernel_integrable index), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index member
    rw [show (∫ value : ℝ in Set.Ioi threshold, kernel index value) =
      (radius index) ^ (-3 - displacement) / (3 + displacement) from
        rpow_tail_indicator_integral threshold (radius index) displacement threshold_positive
          (radius_large index member) displacement_positive]
    field_simp
  rw [sum_identity]
  calc
    _ ≤ (3 + displacement) * ∫ value : ℝ in Set.Ioi threshold, coefficient * value ^ (-1 - displacement) :=
      mul_le_mul_of_nonneg_left bound_integral (by linarith)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) threshold_positive]
      have exponent : -1 - displacement + 1 = -displacement := by ring
      rw [exponent, neg_div_neg_eq]
      ring

theorem power_tsum_le_prefix_and_tail {Index : Type*} (radius : Index → ℝ)
    (positive : ∀ index, 0 < radius index)
    (finite_ball : ∀ value : ℝ, {index | radius index < value}.Finite)
    (threshold coefficient displacement : ℝ)
    (threshold_positive : 0 < threshold) (displacement_positive : 0 < displacement)
    (count_bound : ∀ value : ℝ, threshold < value →
      (({index | radius index < value}.ncard : ℕ) : ℝ) ≤ coefficient * value ^ 3) :
    (∑' index, (radius index) ^ (-3 - displacement)) ≤
      (∑ index ∈ (finite_ball threshold).toFinset, (radius index) ^ (-3 - displacement)) +
        (3 + displacement) * coefficient * threshold ^ (-displacement) / displacement := by
  classical
  apply Real.tsum_le_of_sum_le (fun index => Real.rpow_nonneg (positive index).le _)
  intro indices
  have tail := finite_power_sum_of_count_bound radius (indices.filter (fun index => ¬radius index < threshold))
    threshold coefficient displacement threshold_positive displacement_positive
    (fun index member => le_of_not_gt (Finset.mem_filter.mp member).2) (by
      intro value value_large
      have count_le : ((indices.filter (fun index => ¬radius index < threshold)).filter
          (fun index => radius index < value)).card ≤ {index | radius index < value}.ncard := by
        have subset : (↑((indices.filter (fun index => ¬radius index < threshold)).filter
            (fun index => radius index < value)) : Set Index) ⊆ {index | radius index < value} := by
          intro index member
          exact (Finset.mem_filter.mp member).2
        simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard subset (finite_ball value)
      exact (Nat.cast_le.mpr count_le).trans (count_bound value value_large))
  have initialSum : (∑ index ∈ indices.filter (fun index => radius index < threshold),
      (radius index) ^ (-3 - displacement)) ≤
      ∑ index ∈ (finite_ball threshold).toFinset, (radius index) ^ (-3 - displacement) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro index member
      exact (finite_ball threshold).mem_toFinset.mpr (Finset.mem_filter.mp member).2
    · intro index _ _
      exact Real.rpow_nonneg (positive index).le _
  rw [← Finset.sum_filter_add_sum_filter_not indices (fun index => radius index < threshold)]
  exact add_le_add initialSum tail

theorem power_tsum_boundary_bound_of_counting {Index : Type*} (radius : Index → ℝ)
    (positive : ∀ index, 0 < radius index)
    (finite_ball : ∀ value : ℝ, {index | radius index < value}.Finite)
    (threshold coefficient : ℝ) (threshold_positive : 0 < threshold)
    (count_bound : ∀ value : ℝ, threshold < value →
      (({index | radius index < value}.ncard : ℕ) : ℝ) ≤ coefficient * value ^ 3) :
    ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      displacement * (∑' index, (radius index) ^ (-3 - displacement)) ≤ 3 * coefficient + 1 := by
  classical
  let initialSum (displacement : ℝ) :=
    ∑ index ∈ (finite_ball threshold).toFinset, (radius index) ^ (-3 - displacement)
  have prefix_continuous : Continuous initialSum := by
    apply continuous_finsetSum
    intro index _
    simp only [Real.rpow_def_of_pos (positive index)]
    exact (continuous_const.mul (continuous_const.sub continuous_id)).rexp
  have tail_continuous : Continuous (fun displacement : ℝ => threshold ^ (-displacement)) := by
    simp only [Real.rpow_def_of_pos threshold_positive]
    exact (continuous_const.mul continuous_id.neg).rexp
  have upper_continuous : Continuous (fun displacement : ℝ => displacement * initialSum displacement +
      (3 + displacement) * coefficient * threshold ^ (-displacement)) :=
    (continuous_id.mul prefix_continuous).add
      (((continuous_const.add continuous_id).mul continuous_const).mul tail_continuous)
  have upper_limit : Tendsto (fun displacement : ℝ => displacement * initialSum displacement +
      (3 + displacement) * coefficient * threshold ^ (-displacement))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (3 * coefficient)) := by
    simpa only [zero_mul, zero_add, add_zero, neg_zero, Real.rpow_zero, mul_one] using
      (upper_continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  have upper := upper_limit.eventually (gt_mem_nhds (lt_add_one (3 * coefficient)))
  filter_upwards [self_mem_nhdsWithin, upper] with displacement displacement_positive upper
  change 0 < displacement at displacement_positive
  have estimate := mul_le_mul_of_nonneg_left
    (power_tsum_le_prefix_and_tail radius positive finite_ball threshold coefficient displacement
      threshold_positive displacement_positive count_bound) displacement_positive.le
  calc
    _ ≤ displacement * (initialSum displacement +
        (3 + displacement) * coefficient * threshold ^ (-displacement) / displacement) := estimate
    _ = displacement * initialSum displacement + (3 + displacement) * coefficient * threshold ^ (-displacement) := by
      field_simp
    _ ≤ _ := upper.le

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
