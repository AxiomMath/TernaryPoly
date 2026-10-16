module

public import TernaryPeriodPolynomials.BoundaryComparison.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.AngularIntegral
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Integrability
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Clause3
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Nonvanishing

@[expose] public section


/-! Target: the real constant-term entry of Appendix C.5 (`ar:eq:cinfty`). -/

open MeasureTheory

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Appendix C.5, real entry.** The angular integral is
`∫_0^{2π} e^{ikθ}(c - irv)³(c - iv/r)ⁿ dθ = 2π(r+1)^k/(2^k rⁿ)` for `r > 0`, `k = n + 3`; the
integrand of `I_n` is integrable; and dividing `I_n` by its value `(-1)ⁿ(2i)^{-k}` at `τ = i`
gives `c_∞ = -2πi/(n+1) ≠ 0`. -/
theorem real_constant_term_entry (n : ℕ) :
    (∀ r : ℝ, 0 < r →
      ∫ θ in (0 : ℝ)..(2 * Real.pi), angularIntegrand n r θ =
        2 * Real.pi * ((r : ℂ) + 1) ^ (n + 3) / (2 ^ (n + 3) * (r : ℂ) ^ n)) ∧
    Integrable (entryIntegrand n) ∧
    entryIntegral n / ((-1) ^ n * (2 * Complex.I) ^ (-((n : ℤ) + 3))) =
      -2 * Real.pi * Complex.I / ((n : ℂ) + 1) ∧
    -2 * Real.pi * Complex.I / ((n : ℂ) + 1) ≠ 0 := by
  exact ⟨fun r hr => real_constant_term_entry_clause1 n r hr,
    real_constant_term_entry_clause2 n,
    real_constant_term_entry_clause3 n,
    real_constant_term_nonvanishing n⟩

end TernaryPeriodPolynomials
