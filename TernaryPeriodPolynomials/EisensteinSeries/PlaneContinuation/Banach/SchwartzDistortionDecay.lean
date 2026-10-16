module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.SchwartzLattice

@[expose] public section


namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzDistortionDecay

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]

theorem exists_majorant {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (function : SchwartzMap Space Target) (power : ℕ) :
    ∃ majorant : lattice → ℝ, Summable majorant ∧ (∀ point, 0 ≤ majorant point) ∧
      ∀ (transform : Space →L[ℝ] Space) (distortion : ℝ), 0 ≤ distortion →
        (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) →
        ∀ scale : ℝ, 1 ≤ scale → ∀ point : lattice, point ≠ 0 →
          scale ^ power * ‖function (scale • transform point.val)‖ ≤
            distortion ^ (power + Module.finrank ℤ lattice + 1) * majorant point := by
  let order := power + Module.finrank ℤ lattice + 1
  obtain ⟨bound, positive, decay⟩ := function.decay order 0
  simp only [norm_iteratedFDeriv_zero] at decay
  let majorant : lattice → ℝ := fun point => bound * ‖point‖⁻¹ ^ order
  have summable : Summable majorant :=
    (ZLattice.summable_norm_pow_inv lattice order (by dsimp [order]; omega)).mul_left bound
  refine ⟨majorant, summable, fun _ => mul_nonneg positive.le (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _), ?_⟩
  intro transform distortion distortionNonnegative distortionBound scale scaleLower point nonzero
  have scalePositive : 0 < scale := lt_of_lt_of_le zero_lt_one scaleLower
  have pointPositive : 0 < ‖point.val‖ := norm_pos_iff.mpr (fun h => nonzero (Subtype.ext h))
  have powerBound : scale ^ power ≤ scale ^ order := pow_le_pow_right₀ scaleLower (by dsimp [order]; omega)
  have vectorBound : ‖point.val‖ ^ order ≤ distortion ^ order * ‖transform point.val‖ ^ order := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (distortionBound point.val) order
  have weightedBound : ‖point.val‖ ^ order * (scale ^ power * ‖function (scale • transform point.val)‖) ≤
      distortion ^ order * bound := by
    calc
      _ ≤ (distortion ^ order * ‖transform point.val‖ ^ order) *
          (scale ^ order * ‖function (scale • transform point.val)‖) :=
        mul_le_mul vectorBound (mul_le_mul_of_nonneg_right powerBound (norm_nonneg _))
          (mul_nonneg (pow_nonneg scalePositive.le _) (norm_nonneg _))
          (mul_nonneg (pow_nonneg distortionNonnegative _) (pow_nonneg (norm_nonneg _) _))
      _ = distortion ^ order * (‖scale • transform point.val‖ ^ order *
          ‖function (scale • transform point.val)‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos scalePositive, mul_pow]
        ring
      _ ≤ distortion ^ order * bound := mul_le_mul_of_nonneg_left (decay _) (pow_nonneg distortionNonnegative _)
  change scale ^ power * ‖function (scale • transform point.val)‖ ≤ distortion ^ order * (bound * ‖point.val‖⁻¹ ^ order)
  rw [← mul_assoc, inv_pow, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos pointPositive order)).mpr (by simpa only [mul_comm] using weightedBound)

theorem weighted_sum_bound {Index Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (function : SchwartzMap Space Target) (power : ℕ) (indexMap : Index → lattice)
    (injective : Function.Injective indexMap) (nonzero : ∀ index, indexMap index ≠ 0)
    (weights : Index → ℂ) (bound : ℝ) (bounded : ∀ index, ‖weights index‖ ≤ bound) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (transform : Space →L[ℝ] Space) (distortion : ℝ), 0 ≤ distortion →
        (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) →
        ∀ scale : ℝ, 1 ≤ scale →
          Summable (fun index => ‖weights index • function (scale • transform (indexMap index).val)‖) ∧
          scale ^ power * (∑' index, ‖weights index • function (scale • transform (indexMap index).val)‖) ≤
            constant * distortion ^ (power + Module.finrank ℤ lattice + 1) := by
  obtain ⟨majorant, summableMajorant, nonnegative, majorantBound⟩ := exists_majorant lattice function power
  let constant := ∑' index, max bound 0 * majorant (indexMap index)
  have boundNonnegative : 0 ≤ max bound 0 := le_max_right _ _
  have summableBound : Summable (fun index => max bound 0 * majorant (indexMap index)) :=
    (summableMajorant.comp_injective injective).mul_left _
  refine ⟨constant, tsum_nonneg (fun index => mul_nonneg boundNonnegative (nonnegative _)), ?_⟩
  intro transform distortion distortionNonnegative distortionBound scale scaleLower
  let order := power + Module.finrank ℤ lattice + 1
  have powerNonnegative : 0 ≤ distortion ^ order := pow_nonneg distortionNonnegative _
  have scalePower : 1 ≤ scale ^ power := one_le_pow₀ scaleLower
  have pointBound (index : Index) : scale ^ power *
      ‖weights index • function (scale • transform (indexMap index).val)‖ ≤
        (max bound 0 * majorant (indexMap index)) * distortion ^ order := by
    rw [norm_smul, mul_comm ‖weights index‖, ← mul_assoc]
    calc
      _ ≤ (distortion ^ order * majorant (indexMap index)) * ‖weights index‖ :=
        mul_le_mul_of_nonneg_right (majorantBound transform distortion distortionNonnegative distortionBound
          scale scaleLower _ (nonzero index)) (norm_nonneg _)
      _ ≤ (distortion ^ order * majorant (indexMap index)) * max bound 0 :=
        mul_le_mul_of_nonneg_left ((bounded index).trans (le_max_left _ _)) (mul_nonneg powerNonnegative (nonnegative _))
      _ = _ := by ring
  have summableNorm : Summable (fun index => ‖weights index • function (scale • transform (indexMap index).val)‖) :=
    (summableBound.mul_right (distortion ^ order)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun index =>
      (le_mul_of_one_le_left (norm_nonneg _) scalePower).trans (pointBound index))
  refine ⟨summableNorm, ?_⟩
  calc
    _ = ∑' index, scale ^ power * ‖weights index • function (scale • transform (indexMap index).val)‖ := (tsum_mul_left).symm
    _ ≤ ∑' index, (max bound 0 * majorant (indexMap index)) * distortion ^ order :=
      Summable.tsum_le_tsum pointBound (summableNorm.mul_left _) (summableBound.mul_right _)
    _ = constant * distortion ^ order := tsum_mul_right

theorem uniform_weights {Index Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (function : SchwartzMap Space Target) (power : ℕ) (indexMap : Index → lattice)
    (injective : Function.Injective indexMap) (nonzero : ∀ index, indexMap index ≠ 0) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ weights : Index → ℂ, (∀ index, ‖weights index‖ ≤ bound) →
      ∀ (transform : Space →L[ℝ] Space) (distortion : ℝ), 0 ≤ distortion →
        (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) → ∀ scale : ℝ, 1 ≤ scale →
          Summable (fun index => ‖weights index • function (scale • transform (indexMap index).val)‖) ∧
          scale ^ power * (∑' index, ‖weights index • function (scale • transform (indexMap index).val)‖) ≤
            constant * distortion ^ (power + Module.finrank ℤ lattice + 1) := by
  obtain ⟨constant, nonnegative, bounded⟩ := weighted_sum_bound lattice function power indexMap injective nonzero
    (fun _ => 1) 1 (fun _ => by rw [norm_one])
  have boundNonnegative : 0 ≤ max bound 0 := le_max_right _ _
  refine ⟨max bound 0 * constant, mul_nonneg boundNonnegative nonnegative, ?_⟩
  intro weights weightBound transform distortion distortionNonnegative distortionBound scale scaleLower
  obtain ⟨referenceSummable, referenceBound⟩ := bounded transform distortion distortionNonnegative distortionBound scale scaleLower
  simp only [one_smul] at referenceSummable referenceBound
  have pointBound (index : Index) : ‖weights index • function (scale • transform (indexMap index).val)‖ ≤
      max bound 0 * ‖function (scale • transform (indexMap index).val)‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right ((weightBound index).trans (le_max_left _ _)) (norm_nonneg _)
  have summable := (referenceSummable.mul_left (max bound 0)).of_nonneg_of_le (fun _ => norm_nonneg _) pointBound
  refine ⟨summable, ?_⟩
  calc
    _ ≤ scale ^ power * ∑' index, max bound 0 * ‖function (scale • transform (indexMap index).val)‖ :=
      mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum pointBound summable (referenceSummable.mul_left _))
        (pow_nonneg (zero_le_one.trans scaleLower) _)
    _ = max bound 0 * (scale ^ power * ∑' index, ‖function (scale • transform (indexMap index).val)‖) := by
      rw [tsum_mul_left]; ring
    _ ≤ max bound 0 * (constant * distortion ^ (power + Module.finrank ℤ lattice + 1)) :=
      mul_le_mul_of_nonneg_left referenceBound boundNonnegative
    _ = _ := (mul_assoc _ _ _).symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzDistortionDecay
