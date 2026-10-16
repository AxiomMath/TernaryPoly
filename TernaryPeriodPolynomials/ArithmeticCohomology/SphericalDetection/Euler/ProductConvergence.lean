module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RemovedEulerFactors

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem quadraticEulerFactors_multipliable {index : Type}
    (first second : index → ℂ)
    (first_small : ∀ place, ‖first place‖ < 1)
    (second_small : ∀ place, ‖second place‖ < 1)
    (first_summable : Summable (fun place => ‖first place‖))
    (second_summable : Summable (fun place => ‖second place‖)) :
    Multipliable (fun place => ((1 - first place) * (1 - second place))⁻¹) := by
  let factors := fun place => (1 - first place) * (1 - second place)
  have summable : Summable (fun place => ‖factors place - 1‖) :=
    quadraticEulerFactors_summable_difference first second first_small first_summable second_summable
  have nonzero : (∏' place, factors place) ≠ 0 :=
    eulerProduct_ne_zero_of_summable_difference factors
      (fun place => quadraticEulerFactor_ne_zero (first_small place) (second_small place)) summable
  have identity (place : index) : 1 + (factors place - 1) = factors place := by ring
  have multipliable : Multipliable factors := by
    simpa only [identity] using multipliable_one_add_of_summable summable
  exact multipliable.inv₀ nonzero

theorem outerEulerProduct_restricted_multipliable (first second : Nat.Primes → ℂ)
    (weight argument : ℝ) (included : Nat.Primes → Prop)
    (first_bound : ∀ place, ‖first place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (second_bound : ∀ place, ‖second place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (argument_bound : weight / 2 + 1 < argument) :
    Multipliable (fun place : {place : Nat.Primes // included place} =>
      ((1 - scaledEulerRoot first argument place.val) *
        (1 - scaledEulerRoot second argument place.val))⁻¹) := by
  obtain ⟨first_small, first_summable⟩ := scaledEulerRoot_small_and_summable first weight argument first_bound argument_bound
  obtain ⟨second_small, second_summable⟩ := scaledEulerRoot_small_and_summable second weight argument second_bound argument_bound
  exact quadraticEulerFactors_multipliable _ _
    (fun place => first_small place.val) (fun place => second_small place.val)
    (first_summable.subtype included) (second_summable.subtype included)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
