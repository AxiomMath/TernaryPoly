module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.SolutionDimensions
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section


/-!
# Corollary 1.4, fourth conjunct: the Hilbert series

From the explicit dimension `dim W_n = 2 (r - ⌊r/2⌋ - ⌊r/3⌋ - 1)` for `n = 2r` and `0` for odd
`n` (`finrank_solutionSpace_formula`), the generating function satisfies
`(∑ dim W_n tⁿ) (1 - t⁴)(1 - t⁶) = 2 t¹⁰`.

Formalized by Claude Sonnet 5.5.
-/

open TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument.Corollary14

theorem hilbertSeries_mul (F : Type*) [Field F] [CharZero F] :
    PowerSeries.mk (fun n => (Module.finrank F (solutionSpace F n) : ℤ)) *
        ((1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6)) =
      2 * PowerSeries.X ^ 10 := by
  have hexp : ((1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6) : PowerSeries ℤ) =
      1 - PowerSeries.X ^ 4 - PowerSeries.X ^ 6 + PowerSeries.X ^ 10 := by ring
  rw [hexp]
  ext m
  have key : ∀ k : ℕ, (Module.finrank F (solutionSpace F k) : ℤ) =
      if k % 2 = 0 then 2 * ((k / 2 - k / 2 / 2 - k / 2 / 3 - 1 : ℕ) : ℤ) else 0 :=
    finrank_solutionSpace_formula F
  have h2 : (2 * PowerSeries.X ^ 10 : PowerSeries ℤ) = PowerSeries.C 2 * PowerSeries.X ^ 10 := by
    simp
  rw [h2, mul_add, mul_sub, mul_sub, mul_one, map_add, map_sub, map_sub,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  simp only [PowerSeries.coeff_mk, key]
  split_ifs <;> omega

end TernaryPeriodPolynomials.Argument.Corollary14
