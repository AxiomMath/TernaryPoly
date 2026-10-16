module

public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ModularForm.Periods.GlobalEntryProof

@[expose] public section


/-! Target: the global bad-plane to good-line entry `ar:eq:globalentry` of Appendix C.6. -/

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Appendix C.6, global entry.** For a normalized level-one eigenform `h` of weight
`k = n + 3 > 6`, the entry
`-2πi/(9(n+1)) · L^{(3)}(h, k-2)/L^{(3)}(h, k-1)` is nonzero, where `L^{(3)}` omits the Euler
factor at `3`. -/
theorem global_entry_ne_zero (n : ℕ) (hn : 3 < n) (h : CuspForm levelOne ((n : ℤ) + 3))
    (hh : IsNormalizedEigenform h) :
    -2 * Real.pi * Complex.I / (9 * ((n : ℂ) + 1)) *
      ((LSeries (fun m => fourierCoeff h m) ((n : ℂ) + 1) *
          (1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((n : ℂ) + 1)) + (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 1)))) /
        (LSeries (fun m => fourierCoeff h m) ((n : ℂ) + 2) *
          (1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((n : ℂ) + 2)) + (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 2))))) ≠ 0 :=
  global_entry_ne_zero' n hn h hh

end TernaryPeriodPolynomials
