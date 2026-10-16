module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rational.AdditiveDomain
public import Mathlib.Analysis.Fourier.AddCircleMulti

@[expose] public section


namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzAffineBounds

theorem exists_majorant {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (function : SchwartzMap Space ℂ) (distortion : ℝ) (distortionNonnegative : 0 ≤ distortion) :
    ∃ majorant : lattice → ℝ, Summable majorant ∧ (∀ point, 0 ≤ majorant point) ∧
      ∀ transform : Space → Space, (∀ vector, ‖vector‖ ≤ distortion * (1 + ‖transform vector‖)) →
        ∀ point : lattice, ‖function (transform point.val)‖ ≤ majorant point := by
  classical
  let order := Module.finrank ℤ lattice + 1
  let bound : ℝ := 2 ^ order * ((Finset.Iic (order, 0)).sup fun pair => SchwartzMap.seminorm ℂ pair.1 pair.2) function
  have decay : ∀ vector : Space, (1 + ‖vector‖) ^ order * ‖function vector‖ ≤ bound := by
    intro vector
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (order, 0)) le_rfl le_rfl function vector
  have boundNonnegative : 0 ≤ bound := (by positivity : 0 ≤ (1 + ‖(0 : Space)‖) ^ order * ‖function 0‖).trans (decay 0)
  let majorant : lattice → ℝ := fun point =>
    (if point = 0 then SchwartzMap.seminorm ℂ 0 0 function else 0) + distortion ^ order * bound * ‖point‖⁻¹ ^ order
  have summableDecay := (ZLattice.summable_norm_pow_inv lattice order (Nat.lt_succ_self _)).mul_left
    (distortion ^ order * bound)
  refine ⟨majorant, (hasSum_ite_eq (0 : lattice) (SchwartzMap.seminorm ℂ 0 0 function)).summable.add summableDecay, ?_, ?_⟩
  · intro point
    dsimp [majorant]
    positivity
  · intro transform distortionBound point
    by_cases zeroPoint : point = 0
    · subst point
      simp only [majorant, ite_true, ZeroMemClass.coe_zero]
      exact (SchwartzMap.norm_le_seminorm ℂ function (transform 0)).trans (le_add_of_nonneg_right (by positivity))
    · have normPositive : 0 < ‖point.val‖ := norm_pos_iff.mpr (fun zero => zeroPoint (Subtype.ext zero))
      have powerBound : ‖point.val‖ ^ order ≤ distortion ^ order * (1 + ‖transform point.val‖) ^ order := by
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (distortionBound point.val) order
      have weightedBound : ‖point.val‖ ^ order * ‖function (transform point.val)‖ ≤ distortion ^ order * bound := by
        calc
          _ ≤ (distortion ^ order * (1 + ‖transform point.val‖) ^ order) * ‖function (transform point.val)‖ :=
            mul_le_mul_of_nonneg_right powerBound (norm_nonneg _)
          _ = distortion ^ order * ((1 + ‖transform point.val‖) ^ order * ‖function (transform point.val)‖) := mul_assoc _ _ _
          _ ≤ distortion ^ order * bound := mul_le_mul_of_nonneg_left (decay _) (pow_nonneg distortionNonnegative _)
      simp only [majorant, ite_eq_right zeroPoint, zero_add]
      change ‖function (transform point.val)‖ ≤ distortion ^ order * bound * ‖point.val‖⁻¹ ^ order
      rw [inv_pow, ← div_eq_mul_inv]
      exact (le_div_iff₀ (pow_pos normPositive order)).mpr (by simpa only [mul_comm] using weightedBound)

theorem exists_translate_majorant {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (function : SchwartzMap Space ℂ) (compact : Set Space) (compactIs : IsCompact compact) :
    ∃ majorant : lattice → ℝ, Summable majorant ∧ (∀ point, 0 ≤ majorant point) ∧
      ∀ offset ∈ compact, ∀ point : lattice, ‖function (offset + point.val)‖ ≤ majorant point := by
  obtain ⟨bound, bounded⟩ := compactIs.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨majorant, summableMajorant, nonnegative, majorantBound⟩ :=
    exists_majorant lattice function (1 + max bound 0) (by positivity)
  refine ⟨majorant, summableMajorant, nonnegative, fun offset membership => majorantBound (fun vector => offset + vector) ?_⟩
  intro vector
  have triangle : ‖vector‖ ≤ ‖offset + vector‖ + ‖offset‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le (offset + vector) offset
  have boundOffset : ‖offset‖ ≤ max bound 0 := (bounded offset membership).trans (le_max_left _ _)
  nlinarith [norm_nonneg (offset + vector), le_max_right bound 0]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzAffineBounds
