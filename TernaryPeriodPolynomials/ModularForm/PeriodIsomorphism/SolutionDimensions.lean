module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.EvenBijection
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.SolutionDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularSymDimension

@[expose] public section


/-!
# Corollary 1.4: dimensions of the solution spaces over characteristic-zero fields

* `alternatingSolution_finrank`: `dim_F W_n^{alt}(F) = dim_ℂ S_{n+2}` for every `n` (base change
  from `ℂ` for even `n > 0`, vanishing for `n = 0` or `n` odd).
* `finrank_solutionSpace_formula`: the explicit value of `dim_F W_n(F)`, namely `0` for odd `n` and
  `2 (r - ⌊r/2⌋ - ⌊r/3⌋ - 1)` (truncated subtraction) for `n = 2r`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial TernaryPoly.Paper TernaryPoly.BinaryCuspPeriod

namespace TernaryPeriodPolynomials.Argument.Corollary14

/-- The level-one cusp-form space of weight `2` (the case `n = 0`) is trivial, as a consequence of
the vanishing of the degree-zero symmetric solution space and the symmetric bijection. -/
theorem forms_finrank_zero : Module.finrank ℂ (Forms 0) = 0 := by
  rw [← symmetricSolution_finrank ℂ 0, symmetricSolutionSpace_eq_bot (Or.inl rfl), finrank_bot]

/-- **Corollary 1.4, second conjunct, alternating half.** -/
theorem alternatingSolution_finrank (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    Module.finrank F (alternatingSolutionSpace F n) = Module.finrank ℂ (Forms n) := by
  rcases Nat.even_or_odd n with he | ho
  · by_cases hn0 : n = 0
    · subst hn0
      rw [alternatingSolutionSpace_eq_bot (Or.inl rfl), forms_finrank_zero, finrank_bot]
    · rw [alternatingSolution_finrank_baseChange F n, ← alternatingSolution_finrank_baseChange ℂ n,
        alternatingSolution_finrank_complex n he hn0]
  · rw [alternatingSolutionSpace_eq_bot (Or.inr ho), forms_finrank_eq_zero_of_odd ho, finrank_bot]

theorem finrank_solutionSpace_eq_two_mul (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    Module.finrank F (solutionSpace F n) = 2 * Module.finrank ℂ (Forms n) := by
  rw [finrank_solutionSpace_eq, symmetricSolution_finrank, alternatingSolution_finrank]
  ring

/-- The dimension of the level-one cusp forms of weight `2r + 2`. -/
theorem forms_finrank_even (r : ℕ) :
    Module.finrank ℂ (Forms (2 * r)) = r - r / 2 - r / 3 - 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simpa using forms_finrank_zero
  · have h := TernaryPeriodPolynomials.Spectral.ModularSymDimension.finrank_cuspForm_levelOne
      r hr
    rw [← h]
    exact TernaryPeriodPolynomials.Spectral.ParabolicES.finrank_cuspForm_congr
      (by push_cast; ring)

/-- The explicit dimension of `W_n(F)`. -/
theorem finrank_solutionSpace_formula (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    (Module.finrank F (solutionSpace F n) : ℤ) =
      if n % 2 = 0 then 2 * ((n / 2 - n / 2 / 2 - n / 2 / 3 - 1 : ℕ) : ℤ) else 0 := by
  rw [finrank_solutionSpace_eq_two_mul]
  split_ifs with h
  · obtain ⟨r, hr⟩ : ∃ r, n = 2 * r := ⟨n / 2, by omega⟩
    subst hr
    rw [forms_finrank_even]
    have : 2 * r / 2 = r := by omega
    rw [this]
    omega
  · have ho : Odd n := Nat.odd_iff.mpr (by omega)
    rw [forms_finrank_eq_zero_of_odd ho]
    simp

end TernaryPeriodPolynomials.Argument.Corollary14
