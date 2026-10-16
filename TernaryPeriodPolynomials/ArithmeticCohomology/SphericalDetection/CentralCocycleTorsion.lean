module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleExtension

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G : Type} [Group G]

theorem twoCocycleExtension_torsion_lift (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0)
    (trivial : ∀ element vector, representation.ρ element vector = vector)
    (element : G) (power : ℕ) (positive : 0 < power) (torsion : element ^ power = 1) :
    ∃ lifted : TwoCocycleExtension representation cycle unit_zero,
      twoCocycleExtensionProjection representation cycle unit_zero lifted = element ∧ lifted ^ power = 1 := by
  let initial : TwoCocycleExtension representation cycle unit_zero := ⟨0, element⟩
  let vector : representation := (initial ^ power).coefficient
  let correction := twoCocycleExtensionInclusion representation cycle unit_zero
    (Multiplicative.ofAdd (-((power : ℂ)⁻¹ • vector)))
  have projected : twoCocycleExtensionProjection representation cycle unit_zero (initial ^ power) = 1 := by
    rw [map_pow]
    exact torsion
  have initial_power := twoCocycleExtension_kernel representation cycle unit_zero (initial ^ power) projected
  have commuting : Commute correction initial := twoCocycleExtensionInclusion_commutes representation cycle unit_zero trivial _ _
  refine ⟨correction * initial, ?_, ?_⟩
  · rw [map_mul, twoCocycleExtensionInclusion_projection, one_mul]
    rfl
  · rw [commuting.mul_pow, twoCocycleExtensionInclusion_power, initial_power, ← map_mul]
    change twoCocycleExtensionInclusion representation cycle unit_zero
      (Multiplicative.ofAdd ((power : ℂ) • (-((power : ℂ)⁻¹ • vector)) + vector)) = 1
    rw [smul_neg, smul_smul, mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt positive), one_smul, neg_add_cancel]
    exact (twoCocycleExtensionInclusion representation cycle unit_zero).map_one

theorem twoCocycleExtension_torsion_lift_unique (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0)
    (trivial : ∀ element vector, representation.ρ element vector = vector)
    (first second : TwoCocycleExtension representation cycle unit_zero)
    (same : twoCocycleExtensionProjection representation cycle unit_zero first =
      twoCocycleExtensionProjection representation cycle unit_zero second)
    (power : ℕ) (positive : 0 < power) (first_power : first ^ power = 1) (second_power : second ^ power = 1) :
    first = second := by
  have kernel : twoCocycleExtensionProjection representation cycle unit_zero (first * second⁻¹) = 1 := by
    rw [map_mul, map_inv, same, mul_inv_cancel]
  have commuting : Commute (first * second⁻¹) second := by
    rw [twoCocycleExtension_kernel representation cycle unit_zero (first * second⁻¹) kernel]
    exact twoCocycleExtensionInclusion_commutes representation cycle unit_zero trivial _ _
  have difference_power : (first * second⁻¹) ^ power = 1 := by
    have equation := commuting.mul_pow power
    rw [inv_mul_cancel_right, first_power, second_power, mul_one] at equation
    exact equation.symm
  exact mul_inv_eq_one.mp
    (twoCocycleExtension_torsion_kernel representation cycle unit_zero _ kernel power positive difference_power)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
