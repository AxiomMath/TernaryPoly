module

public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ModularForm.Periods.OuterLValues

@[expose] public section


/-! Target: Lemma 2.5 (`lem:outer-values`) of the paper. -/

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Lemma 2.5.** If `h` is a normalized level-one cusp eigenform of weight `k > 6`, then
`L(h, k-2)` and `L(h, k-1)` are nonzero. The same holds after omitting any finite set `S` of
Euler factors: `L^S(h,s) = L(h,s) ∏_{p ∈ S} (1 - a_h(p) p^{-s} + p^{k-1-2s}) ≠ 0` at
`s = k-2, k-1`. -/
theorem lSeries_outer_critical_ne_zero {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k) (hh : IsNormalizedEigenform h)
    (S : Finset Nat.Primes) (s : ℂ) (hs : s = (k : ℂ) - 2 ∨ s = (k : ℂ) - 1) :
    LSeries (fun m => fourierCoeff h m) s *
      ∏ p ∈ S, (1 - fourierCoeff h (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)) +
        ((p : ℕ) : ℂ) ^ ((k : ℂ) - 1 - 2 * s)) ≠ 0 :=
  lemma_2_5' hk h hh S s hs

end TernaryPeriodPolynomials
