module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Theta.ScalingPoisson

@[expose] public section


open scoped Classical

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzScalingDecay

theorem exists_majorant {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (function : SchwartzMap Space ℂ) (power : ℕ) :
    ∃ majorant : lattice → ℝ, Summable majorant ∧ (∀ point, 0 ≤ majorant point) ∧
      ∀ scale : ℝ, 1 ≤ scale → ∀ point : lattice, point ≠ 0 →
        scale ^ power * ‖function (scale • point.val)‖ ≤ majorant point := by
  let order := power + Module.finrank ℤ lattice + 1
  obtain ⟨bound, positive, decay⟩ := function.decay order 0
  simp only [norm_iteratedFDeriv_zero] at decay
  let majorant : lattice → ℝ := fun point => bound * ‖point‖⁻¹ ^ order
  have summable : Summable majorant :=
    (ZLattice.summable_norm_pow_inv lattice order (by dsimp [order]; omega)).mul_left bound
  refine ⟨majorant, summable, fun _ => mul_nonneg positive.le (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _), ?_⟩
  intro scale scaleLower point nonzero
  have scalePositive : 0 < scale := lt_of_lt_of_le zero_lt_one scaleLower
  have pointPositive : 0 < ‖point.val‖ := norm_pos_iff.mpr (fun h => nonzero (Subtype.ext h))
  have powerBound : scale ^ power ≤ scale ^ order := pow_le_pow_right₀ scaleLower (by dsimp [order]; omega)
  have decayBound : ‖point.val‖ ^ order * (scale ^ power * ‖function (scale • point.val)‖) ≤ bound := by
    calc
      _ ≤ ‖point.val‖ ^ order * (scale ^ order * ‖function (scale • point.val)‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right powerBound (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _)
      _ = ‖scale • point.val‖ ^ order * ‖function (scale • point.val)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos scalePositive, mul_pow]
        ring
      _ ≤ bound := decay _
  change scale ^ power * ‖function (scale • point.val)‖ ≤ bound * ‖point.val‖⁻¹ ^ order
  rw [inv_pow, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos pointPositive order)).mpr (by simpa only [mul_comm] using decayBound)

theorem weighted_sum_bound {Index Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (function : SchwartzMap Space ℂ) (power : ℕ) (indexMap : Index → lattice)
    (injective : Function.Injective indexMap) (nonzero : ∀ index, indexMap index ≠ 0)
    (weights : Index → ℂ) (bound : ℝ) (bounded : ∀ index, ‖weights index‖ ≤ bound) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ scale : ℝ, 1 ≤ scale →
      Summable (fun index => ‖function (scale • (indexMap index).val) * weights index‖) ∧
      scale ^ power * ‖∑' index, function (scale • (indexMap index).val) * weights index‖ ≤ constant := by
  obtain ⟨majorant, summableMajorant, nonnegative, majorantBound⟩ := exists_majorant lattice function power
  let constant := ∑' index, max bound 0 * majorant (indexMap index)
  have boundNonnegative : 0 ≤ max bound 0 := le_max_right _ _
  have summableBound : Summable (fun index => max bound 0 * majorant (indexMap index)) :=
    (summableMajorant.comp_injective injective).mul_left _
  refine ⟨constant, tsum_nonneg (fun index => mul_nonneg boundNonnegative (nonnegative _)), ?_⟩
  intro scale scaleLower
  have scaleNonnegative : 0 ≤ scale := (by norm_num : (0 : ℝ) ≤ 1).trans scaleLower
  have scalePower : 1 ≤ scale ^ power := one_le_pow₀ scaleLower
  have pointBound (index : Index) : scale ^ power *
      ‖function (scale • (indexMap index).val) * weights index‖ ≤ max bound 0 * majorant (indexMap index) := by
    rw [norm_mul, ← mul_assoc]
    calc
      _ ≤ majorant (indexMap index) * ‖weights index‖ :=
        mul_le_mul_of_nonneg_right (majorantBound scale scaleLower _ (nonzero index)) (norm_nonneg _)
      _ ≤ majorant (indexMap index) * max bound 0 :=
        mul_le_mul_of_nonneg_left ((bounded index).trans (le_max_left _ _)) (nonnegative _)
      _ = _ := mul_comm _ _
  have summableNorm : Summable (fun index => ‖function (scale • (indexMap index).val) * weights index‖) :=
    summableBound.of_nonneg_of_le (fun _ => norm_nonneg _) (fun index =>
      (le_mul_of_one_le_left (norm_nonneg _) scalePower).trans (pointBound index))
  refine ⟨summableNorm, ?_⟩
  calc
    _ ≤ scale ^ power * ∑' index, ‖function (scale • (indexMap index).val) * weights index‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm summableNorm) (pow_nonneg scaleNonnegative _)
    _ = ∑' index, scale ^ power * ‖function (scale • (indexMap index).val) * weights index‖ := (tsum_mul_left).symm
    _ ≤ constant := Summable.tsum_le_tsum pointBound (summableNorm.mul_left _) summableBound

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzScalingDecay
