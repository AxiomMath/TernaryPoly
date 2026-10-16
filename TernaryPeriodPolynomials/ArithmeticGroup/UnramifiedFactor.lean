module

public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ModularForm.Periods.UnramifiedFactorProof

@[expose] public section


/-! Target: the unramified local factors of Appendix C.6 (the shell sum before
`ar:eq:globalentry`). -/

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Appendix C.6, unramified factor.** For a normalized level-one eigenform `h` of weight
`k > 6` and a prime `p`, the shells of valuation `r ≥ 1` contribute
`(1 - p⁻¹) p^{-r(k-2)} (a_h(p^r) - p^{k-2} a_h(p^{r-2}))` (with `a_h(p^{-1}) = 0`), the series
converges, and together with the contribution `1` of `ℤ_p²` it sums to
`c_p = L_p(h, k-2)/L_p(h, k-1) =
(1 - a_h(p) p^{1-k} + p^{1-k}) / (1 - a_h(p) p^{2-k} + p^{3-k})`. -/
theorem unramified_local_factor {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k)
    (hh : IsNormalizedEigenform h) (p : Nat.Primes) :
    Summable (fun r : ℕ => ((p : ℕ) : ℂ) ^ (-(((r : ℤ) + 1) * (k - 2))) *
      (fourierCoeff h ((p : ℕ) ^ (r + 1)) -
        ((p : ℕ) : ℂ) ^ (k - 2) * (if r = 0 then 0 else fourierCoeff h ((p : ℕ) ^ (r - 1))))) ∧
    1 + (1 - ((p : ℕ) : ℂ)⁻¹) * ∑' r : ℕ, ((p : ℕ) : ℂ) ^ (-(((r : ℤ) + 1) * (k - 2))) *
      (fourierCoeff h ((p : ℕ) ^ (r + 1)) -
        ((p : ℕ) : ℂ) ^ (k - 2) * (if r = 0 then 0 else fourierCoeff h ((p : ℕ) ^ (r - 1)))) =
    (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (1 - k) + ((p : ℕ) : ℂ) ^ (1 - k)) /
      (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k)) := by
  exact unramified_local_factor' hk h hh p

end TernaryPeriodPolynomials
