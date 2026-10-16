module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.s.GlobalRealizationConv

@[expose] public section


/-! Target: the constant-term identities `ar:eq:constantterms` of Appendix C.4 of the
the paper, in the project's boundary model. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Constant terms (`ar:eq:constantterms`).** For `n ≥ 4`, every mixed cuspidal plane class
`ξ ∈ 𝒞_P(E)` is the plane restriction `r_P 𝓔_P(ξ) = ξ` of a global class whose restriction to
every complete flag vanishes (`r_B 𝓔_P(ξ) = 0`), so that its line restriction `r_Q 𝓔_P(ξ)` is again
mixed cuspidal. -/
theorem constant_terms (n : ℕ) (hn : 4 ≤ n) (ξ : StratumH2 n trivialCharacter .plane)
    (hξ : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      (globalCoordinates n trivialCharacter c).1 = ξ ∧
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 := by
  exact TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Consumers.constant_terms_conv
    n hn ξ hξ

end TernaryPeriodPolynomials
