module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.SchwartzPoisson

@[expose] public section


namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzLattice

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]

theorem summable_norm_transform {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (transform : Space ≃L[ℝ] Space) (function : SchwartzMap Space Target) :
    Summable (fun point : lattice => ‖function (transform point.val)‖) := by
  simpa only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply] using
    BanachSchwartzPoisson.summable_norm_lattice lattice (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ transform function)

theorem exists_uniform_majorant {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (function : SchwartzMap Space Target) (distortion : ℝ) (distortionNonnegative : 0 ≤ distortion) :
    ∃ majorant : lattice → ℝ, Summable majorant ∧ (∀ point, 0 ≤ majorant point) ∧
      ∀ transform : Space →L[ℝ] Space, (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) →
        ∀ point : lattice, ‖function (transform point.val)‖ ≤ majorant point := by
  classical
  let order := Module.finrank ℤ lattice + 1
  obtain ⟨bound, positive, decay⟩ := function.decay order 0
  simp only [norm_iteratedFDeriv_zero] at decay
  let majorant : lattice → ℝ := fun point =>
    (if point = 0 then ‖function 0‖ else 0) + distortion ^ order * bound * ‖point‖⁻¹ ^ order
  have summableDecay := (ZLattice.summable_norm_pow_inv lattice order (Nat.lt_succ_self _)).mul_left
    (distortion ^ order * bound)
  refine ⟨majorant, (hasSum_ite_eq (0 : lattice) ‖function 0‖).summable.add summableDecay, ?_, ?_⟩
  · intro point
    dsimp [majorant]
    positivity
  · intro transform distortionBound point
    by_cases zeroPoint : point = 0
    · subst point
      simp only [majorant, ite_true, ZeroMemClass.coe_zero, map_zero]
      exact le_add_of_nonneg_right (by positivity)
    · have normPositive : 0 < ‖point.val‖ := norm_pos_iff.mpr (fun zero => zeroPoint (Subtype.ext zero))
      have powerBound : ‖point.val‖ ^ order ≤ distortion ^ order * ‖transform point.val‖ ^ order := by
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (distortionBound point.val) order
      have weightedBound : ‖point.val‖ ^ order * ‖function (transform point.val)‖ ≤ distortion ^ order * bound := by
        calc
          _ ≤ (distortion ^ order * ‖transform point.val‖ ^ order) * ‖function (transform point.val)‖ :=
            mul_le_mul_of_nonneg_right powerBound (norm_nonneg _)
          _ = distortion ^ order * (‖transform point.val‖ ^ order * ‖function (transform point.val)‖) := mul_assoc _ _ _
          _ ≤ distortion ^ order * bound := mul_le_mul_of_nonneg_left (decay _) (pow_nonneg distortionNonnegative _)
      simp only [majorant, ite_eq_right zeroPoint, zero_add]
      change ‖function (transform point.val)‖ ≤ distortion ^ order * bound * ‖point.val‖⁻¹ ^ order
      rw [inv_pow, ← div_eq_mul_inv]
      exact (le_div_iff₀ (pow_pos normPositive order)).mpr (by simpa only [mul_comm] using weightedBound)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzLattice
