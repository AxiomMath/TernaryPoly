module

public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ModularForm.Periods.OuterLValues

@[expose] public section


/-!
# Appendix C.6 global entry: nonvanishing

Proof of `global_entry_ne_zero` (target (e)) as a direct corollary of `lSeries_outer_critical_ne_zero` (target (a))
with the omitted-factor set `S = {3}`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument

/-- The prime `3`, as an element of `Nat.Primes`. -/
def primeThree : Nat.Primes := ⟨3, by decide⟩

theorem global_entry_ne_zero' (n : ℕ) (hn : 3 < n) (h : CuspForm levelOne ((n : ℤ) + 3))
    (hh : IsNormalizedEigenform h) :
    -2 * Real.pi * Complex.I / (9 * ((n : ℂ) + 1)) *
      ((LSeries (fun m => fourierCoeff h m) ((n : ℂ) + 1) *
          (1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((n : ℂ) + 1)) +
            (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 1)))) /
        (LSeries (fun m => fourierCoeff h m) ((n : ℂ) + 2) *
          (1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((n : ℂ) + 2)) +
            (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 2))))) ≠ 0 := by
  have hk : (6 : ℤ) < (n : ℤ) + 3 := by omega
  have hA := lemma_2_5' hk h hh {primeThree} ((n : ℂ) + 1) (Or.inl (by push_cast; ring))
  have hB := lemma_2_5' hk h hh {primeThree} ((n : ℂ) + 2) (Or.inr (by push_cast; ring))
  simp only [Finset.prod_singleton, show (primeThree : ℕ) = 3 from rfl, Nat.cast_ofNat] at hA hB
  have eA : (((n : ℤ) + 3 : ℤ) : ℂ) - 1 - 2 * ((n : ℂ) + 1) =
      (n : ℂ) + 2 - 2 * ((n : ℂ) + 1) := by push_cast; ring
  have eB : (((n : ℤ) + 3 : ℤ) : ℂ) - 1 - 2 * ((n : ℂ) + 2) =
      (n : ℂ) + 2 - 2 * ((n : ℂ) + 2) := by push_cast; ring
  rw [eA] at hA
  rw [eB] at hB
  have hcoef : (-2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hdenom : (9 : ℂ) * ((n : ℂ) + 1) ≠ 0 := by
    refine mul_ne_zero (by norm_num) ?_
    have hcast : ((n : ℕ) : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast (Nat.succ_ne_zero n)
  exact mul_ne_zero (div_ne_zero hcoef hdenom) (div_ne_zero hA hB)

end TernaryPeriodPolynomials.Argument
