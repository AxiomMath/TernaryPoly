module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.RCLike
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.Topology.Algebra.InfiniteSum.Field

@[expose] public section


namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem one_sub_ne_zero_of_norm_lt_one {value : ℂ} (small : ‖value‖ < 1) :
    1 - value ≠ 0 := by
  intro zero
  have value_one : value = 1 := (sub_eq_zero.mp zero).symm
  simp only [value_one, norm_one, lt_self_iff_false] at small

theorem quadraticEulerFactor_ne_zero {first second : ℂ}
    (first_small : ‖first‖ < 1) (second_small : ‖second‖ < 1) :
    (1 - first) * (1 - second) ≠ 0 :=
  mul_ne_zero (one_sub_ne_zero_of_norm_lt_one first_small)
    (one_sub_ne_zero_of_norm_lt_one second_small)

theorem eulerProduct_ne_zero_of_summable_difference {index : Type}
    (factors : index → ℂ) (nonzero : ∀ place, factors place ≠ 0)
    (summable : Summable (fun place => ‖factors place - 1‖)) :
    (∏' place, factors place) ≠ 0 := by
  have factor_identity (place : index) : 1 + (factors place - 1) = factors place := by
    ring
  have factor_nonzero : ∀ place, 1 + (factors place - 1) ≠ 0 := by
    intro place
    rw [factor_identity]
    exact nonzero place
  simpa only [factor_identity] using
    tprod_one_add_ne_zero_of_summable factor_nonzero summable

theorem eulerValue_ne_zero_of_hasProd {index : Type}
    (factors : index → ℂ) (value : ℂ) (product : HasProd factors value)
    (nonzero : ∀ place, factors place ≠ 0)
    (summable : Summable (fun place => ‖factors place - 1‖)) : value ≠ 0 := by
  rw [← product.tprod_eq]
  exact eulerProduct_ne_zero_of_summable_difference factors nonzero summable

theorem eulerProduct_away_three_ne_zero
    (factors : Nat.Primes → ℂ) (nonzero : ∀ place, factors place ≠ 0)
    (summable : Summable (fun place => ‖factors place - 1‖)) :
    (∏' place : {place : Nat.Primes // place.val ≠ 3}, factors place.val) ≠ 0 := by
  apply eulerProduct_ne_zero_of_summable_difference
    (fun place : {place : Nat.Primes // place.val ≠ 3} => factors place.val)
  · intro place
    exact nonzero place.val
  · exact summable.subtype (fun place : Nat.Primes => place.val ≠ 3)

theorem local_global_coefficient_ne_zero
    (archimedean numerator denominator : ℂ)
    (archimedean_nonzero : archimedean ≠ 0)
    (numerator_nonzero : numerator ≠ 0) (denominator_nonzero : denominator ≠ 0) :
    (1 / 9 : ℂ) * archimedean * (numerator / denominator) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) archimedean_nonzero)
    (div_ne_zero numerator_nonzero denominator_nonzero)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
