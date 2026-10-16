module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.SchwartzBounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.SchwartzDistortionDecay

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformSchwartzLattice

variable {Space Target : Type}
variable [NormedAddCommGroup Space] [NormedSpace ℝ Space] [FiniteDimensional ℝ Space]
variable [NormedAddCommGroup Target] [NormedSpace ℝ Target] [NormedSpace ℂ Target] [SMulCommClass ℝ ℂ Target]

theorem exists_majorant (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (tests : Set (SchwartzMap Space Target)) (bounded : UniformSchwartzBounds.Bounded tests) (power : ℕ) :
    ∃ majorant : lattice → ℝ, Summable majorant ∧ (∀ point, 0 ≤ majorant point) ∧
      ∀ test ∈ tests, ∀ (transform : Space →L[ℝ] Space) (distortion : ℝ), 0 ≤ distortion →
        (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) →
        ∀ scale : ℝ, 1 ≤ scale → ∀ point : lattice, point ≠ 0 →
          scale ^ power * ‖test (scale • transform point.val)‖ ≤
            distortion ^ (power + Module.finrank ℤ lattice + 1) * majorant point := by
  let order := power + Module.finrank ℤ lattice + 1
  obtain ⟨bound, nonnegative, decay⟩ := UniformSchwartzBounds.norm_pow_bound tests bounded order
  let majorant : lattice → ℝ := fun point => bound * ‖point‖⁻¹ ^ order
  have summable : Summable majorant :=
    (ZLattice.summable_norm_pow_inv lattice order (by dsimp [order]; omega)).mul_left bound
  refine ⟨majorant, summable, fun _ => mul_nonneg nonnegative (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _), ?_⟩
  intro test membership transform distortion distortionNonnegative distortionBound scale scaleLower point nonzero
  have scalePositive : 0 < scale := lt_of_lt_of_le zero_lt_one scaleLower
  have pointPositive : 0 < ‖point.val‖ := norm_pos_iff.mpr (fun h => nonzero (Subtype.ext h))
  have powerBound : scale ^ power ≤ scale ^ order := pow_le_pow_right₀ scaleLower (by dsimp [order]; omega)
  have vectorBound : ‖point.val‖ ^ order ≤ distortion ^ order * ‖transform point.val‖ ^ order := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (distortionBound point.val) order
  have weightedBound : ‖point.val‖ ^ order * (scale ^ power * ‖test (scale • transform point.val)‖) ≤
      distortion ^ order * bound := by
    calc
      _ ≤ (distortion ^ order * ‖transform point.val‖ ^ order) *
          (scale ^ order * ‖test (scale • transform point.val)‖) :=
        mul_le_mul vectorBound (mul_le_mul_of_nonneg_right powerBound (norm_nonneg _))
          (mul_nonneg (pow_nonneg scalePositive.le _) (norm_nonneg _))
          (mul_nonneg (pow_nonneg distortionNonnegative _) (pow_nonneg (norm_nonneg _) _))
      _ = distortion ^ order * (‖scale • transform point.val‖ ^ order *
          ‖test (scale • transform point.val)‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos scalePositive, mul_pow]
        ring
      _ ≤ distortion ^ order * bound := mul_le_mul_of_nonneg_left (decay test membership _) (pow_nonneg distortionNonnegative _)
  change scale ^ power * ‖test (scale • transform point.val)‖ ≤ distortion ^ order * (bound * ‖point.val‖⁻¹ ^ order)
  rw [← mul_assoc, inv_pow, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos pointPositive order)).mpr (by simpa only [mul_comm] using weightedBound)

theorem uniform_weights {Index : Type} (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (tests : Set (SchwartzMap Space Target)) (bounded : UniformSchwartzBounds.Bounded tests)
    (power : ℕ) (indexMap : Index → lattice) (injective : Function.Injective indexMap)
    (nonzero : ∀ index, indexMap index ≠ 0) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ test ∈ tests, ∀ weights : Index → ℂ,
      (∀ index, ‖weights index‖ ≤ bound) →
      ∀ (transform : Space →L[ℝ] Space) (distortion : ℝ), 0 ≤ distortion →
        (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) → ∀ scale : ℝ, 1 ≤ scale →
          Summable (fun index => ‖weights index • test (scale • transform (indexMap index).val)‖) ∧
          scale ^ power * (∑' index, ‖weights index • test (scale • transform (indexMap index).val)‖) ≤
            constant * distortion ^ (power + Module.finrank ℤ lattice + 1) := by
  obtain ⟨majorant, summableMajorant, nonnegative, majorantBound⟩ := exists_majorant lattice tests bounded power
  let constant := ∑' index, max bound 0 * majorant (indexMap index)
  have boundNonnegative : 0 ≤ max bound 0 := le_max_right _ _
  have summableBound : Summable (fun index => max bound 0 * majorant (indexMap index)) :=
    (summableMajorant.comp_injective injective).mul_left _
  refine ⟨constant, tsum_nonneg (fun index => mul_nonneg boundNonnegative (nonnegative _)), ?_⟩
  intro test membership weights weightBound transform distortion distortionNonnegative distortionBound scale scaleLower
  let order := power + Module.finrank ℤ lattice + 1
  have powerNonnegative : 0 ≤ distortion ^ order := pow_nonneg distortionNonnegative _
  have scalePower : 1 ≤ scale ^ power := one_le_pow₀ scaleLower
  have pointBound (index : Index) : scale ^ power *
      ‖weights index • test (scale • transform (indexMap index).val)‖ ≤
        (max bound 0 * majorant (indexMap index)) * distortion ^ order := by
    rw [norm_smul, mul_comm ‖weights index‖, ← mul_assoc]
    calc
      _ ≤ (distortion ^ order * majorant (indexMap index)) * ‖weights index‖ :=
        mul_le_mul_of_nonneg_right (majorantBound test membership transform distortion distortionNonnegative distortionBound
          scale scaleLower _ (nonzero index)) (norm_nonneg _)
      _ ≤ (distortion ^ order * majorant (indexMap index)) * max bound 0 :=
        mul_le_mul_of_nonneg_left ((weightBound index).trans (le_max_left _ _)) (mul_nonneg powerNonnegative (nonnegative _))
      _ = _ := by ring
  have summableNorm : Summable (fun index => ‖weights index • test (scale • transform (indexMap index).val)‖) :=
    (summableBound.mul_right (distortion ^ order)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun index =>
      (le_mul_of_one_le_left (norm_nonneg _) scalePower).trans (pointBound index))
  refine ⟨summableNorm, ?_⟩
  calc
    _ = ∑' index, scale ^ power * ‖weights index • test (scale • transform (indexMap index).val)‖ := (tsum_mul_left).symm
    _ ≤ ∑' index, (max bound 0 * majorant (indexMap index)) * distortion ^ order :=
      Summable.tsum_le_tsum pointBound (summableNorm.mul_left _) (summableBound.mul_right _)
    _ = constant * distortion ^ order := tsum_mul_right

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformSchwartzLattice
