module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Euler.Nonvanishing
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Data.Nat.Squarefree

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem quadraticEulerFactors_summable_difference {index : Type}
    (first second : index → ℂ)
    (first_small : ∀ place, ‖first place‖ < 1)
    (first_summable : Summable (fun place => ‖first place‖))
    (second_summable : Summable (fun place => ‖second place‖)) :
    Summable (fun place => ‖(1 - first place) * (1 - second place) - 1‖) := by
  apply Summable.of_nonneg_of_le (fun place => norm_nonneg _)
    (fun place => ?_) (first_summable.add (second_summable.mul_left 2))
  have identity : (1 - first place) * (1 - second place) - 1 =
      -(first place) - second place + first place * second place := by ring
  rw [identity]
  calc
    ‖-(first place) - second place + first place * second place‖ ≤
        ‖-(first place) - second place‖ + ‖first place * second place‖ := norm_add_le _ _
    _ ≤ (‖first place‖ + ‖second place‖) + ‖first place‖ * ‖second place‖ := by
      rw [norm_mul]
      simpa only [norm_neg, add_comm] using
        add_le_add_right (norm_sub_le (-first place) (second place))
          (‖first place‖ * ‖second place‖)
    _ ≤ ‖first place‖ + 2 * ‖second place‖ := by
      have bound := mul_le_mul_of_nonneg_right (first_small place).le
        (norm_nonneg (second place))
      linarith

theorem quadraticEulerProduct_ne_zero_of_summable_roots {index : Type}
    (first second : index → ℂ)
    (first_small : ∀ place, ‖first place‖ < 1)
    (second_small : ∀ place, ‖second place‖ < 1)
    (first_summable : Summable (fun place => ‖first place‖))
    (second_summable : Summable (fun place => ‖second place‖)) :
    (∏' place, ((1 - first place) * (1 - second place))⁻¹) ≠ 0 := by
  let factors := fun place => (1 - first place) * (1 - second place)
  have difference_summable : Summable (fun place => ‖factors place - 1‖) :=
    quadraticEulerFactors_summable_difference first second first_small
      first_summable second_summable
  have factors_nonzero : ∀ place, factors place ≠ 0 := fun place =>
    quadraticEulerFactor_ne_zero (first_small place) (second_small place)
  have product_nonzero := eulerProduct_ne_zero_of_summable_difference factors
    factors_nonzero difference_summable
  have identity (place : index) : 1 + (factors place - 1) = factors place := by ring
  have product_exists : Multipliable factors := by
    simpa only [identity] using multipliable_one_add_of_summable difference_summable
  rw [product_exists.tprod_inv₀ product_nonzero]
  exact inv_ne_zero product_nonzero

def scaledEulerRoot (root : Nat.Primes → ℂ) (argument : ℝ) (place : Nat.Primes) : ℂ :=
  root place * (((place.val : ℝ) ^ (-argument) : ℝ) : ℂ)

theorem scaledEulerRoot_norm_bound (root : Nat.Primes → ℂ) (weight argument : ℝ)
    (root_bound : ∀ place, ‖root place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (place : Nat.Primes) :
    ‖scaledEulerRoot root argument place‖ ≤ (place.val : ℝ) ^ (weight / 2 - argument) := by
  have prime_positive : (0 : ℝ) < place.val := by exact_mod_cast place.property.pos
  rw [scaledEulerRoot, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg prime_positive.le _)]
  calc
    ‖root place‖ * (place.val : ℝ) ^ (-argument) ≤
        (place.val : ℝ) ^ (weight / 2) * (place.val : ℝ) ^ (-argument) :=
      mul_le_mul_of_nonneg_right (root_bound place) (Real.rpow_nonneg prime_positive.le _)
    _ = (place.val : ℝ) ^ (weight / 2 - argument) := by
      rw [← Real.rpow_add prime_positive]
      rfl

theorem scaledEulerRoot_small_and_summable (root : Nat.Primes → ℂ)
    (weight argument : ℝ)
    (root_bound : ∀ place, ‖root place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (argument_bound : weight / 2 + 1 < argument) :
    (∀ place, ‖scaledEulerRoot root argument place‖ < 1) ∧
      Summable (fun place => ‖scaledEulerRoot root argument place‖) := by
  have exponent_bound : weight / 2 - argument < -1 := by linarith
  constructor
  · intro place
    apply lt_of_le_of_lt (scaledEulerRoot_norm_bound root weight argument root_bound place)
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast place.property.one_lt
    · linarith
  · exact Summable.of_nonneg_of_le (fun place => norm_nonneg _)
      (scaledEulerRoot_norm_bound root weight argument root_bound)
      (Nat.Primes.summable_rpow.mpr exponent_bound)

theorem outerEulerProduct_ne_zero (first second : Nat.Primes → ℂ)
    (weight argument : ℝ)
    (first_bound : ∀ place, ‖first place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (second_bound : ∀ place, ‖second place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (argument_bound : weight / 2 + 1 < argument) :
    (∏' place, ((1 - scaledEulerRoot first argument place) *
      (1 - scaledEulerRoot second argument place))⁻¹) ≠ 0 := by
  obtain ⟨first_small, first_summable⟩ :=
    scaledEulerRoot_small_and_summable first weight argument first_bound argument_bound
  obtain ⟨second_small, second_summable⟩ :=
    scaledEulerRoot_small_and_summable second weight argument second_bound argument_bound
  exact quadraticEulerProduct_ne_zero_of_summable_roots _ _ first_small second_small
    first_summable second_summable

theorem outerEulerProduct_restricted_ne_zero (first second : Nat.Primes → ℂ)
    (weight argument : ℝ) (included : Nat.Primes → Prop)
    (first_bound : ∀ place, ‖first place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (second_bound : ∀ place, ‖second place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (argument_bound : weight / 2 + 1 < argument) :
    (∏' place : {place : Nat.Primes // included place},
      ((1 - scaledEulerRoot first argument place.val) *
        (1 - scaledEulerRoot second argument place.val))⁻¹) ≠ 0 := by
  obtain ⟨first_small, first_summable⟩ :=
    scaledEulerRoot_small_and_summable first weight argument first_bound argument_bound
  obtain ⟨second_small, second_summable⟩ :=
    scaledEulerRoot_small_and_summable second weight argument second_bound argument_bound
  exact quadraticEulerProduct_ne_zero_of_summable_roots _ _
    (fun place => first_small place.val) (fun place => second_small place.val)
    (first_summable.subtype included) (second_summable.subtype included)

theorem outerCriticalEulerProducts_away_three_ne_zero
    (first second : Nat.Primes → ℂ) (weight : ℝ)
    (weight_bound : 6 < weight)
    (first_bound : ∀ place, ‖first place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (second_bound : ∀ place, ‖second place‖ ≤ (place.val : ℝ) ^ (weight / 2)) :
    (∏' place : {place : Nat.Primes // place.val ≠ 3},
      ((1 - scaledEulerRoot first (weight - 2) place.val) *
        (1 - scaledEulerRoot second (weight - 2) place.val))⁻¹) ≠ 0 ∧
    (∏' place : {place : Nat.Primes // place.val ≠ 3},
      ((1 - scaledEulerRoot first (weight - 1) place.val) *
        (1 - scaledEulerRoot second (weight - 1) place.val))⁻¹) ≠ 0 := by
  constructor
  · exact outerEulerProduct_restricted_ne_zero first second weight (weight - 2)
      (fun place => place.val ≠ 3) first_bound second_bound (by linarith)
  · exact outerEulerProduct_restricted_ne_zero first second weight (weight - 1)
      (fun place => place.val ≠ 3) first_bound second_bound (by linarith)

theorem standardOuterEulerCoefficient_ne_zero
    (first second : Nat.Primes → ℂ) (weight : ℝ) (archimedean : ℂ)
    (weight_bound : 6 < weight) (archimedean_nonzero : archimedean ≠ 0)
    (first_bound : ∀ place, ‖first place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (second_bound : ∀ place, ‖second place‖ ≤ (place.val : ℝ) ^ (weight / 2)) :
    (1 / 9 : ℂ) * archimedean *
      ((∏' place : {place : Nat.Primes // place.val ≠ 3},
        ((1 - scaledEulerRoot first (weight - 2) place.val) *
          (1 - scaledEulerRoot second (weight - 2) place.val))⁻¹) /
      (∏' place : {place : Nat.Primes // place.val ≠ 3},
        ((1 - scaledEulerRoot first (weight - 1) place.val) *
          (1 - scaledEulerRoot second (weight - 1) place.val))⁻¹)) ≠ 0 := by
  obtain ⟨numerator_nonzero, denominator_nonzero⟩ :=
    outerCriticalEulerProducts_away_three_ne_zero first second weight weight_bound
      first_bound second_bound
  exact local_global_coefficient_ne_zero archimedean _ _ archimedean_nonzero
    numerator_nonzero denominator_nonzero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
