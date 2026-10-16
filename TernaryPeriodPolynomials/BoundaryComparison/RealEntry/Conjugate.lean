module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.ConjScalar
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBridgeConj

@[expose] public section


/-!
# The conjugate component of the real entry has the conjugate scalar

* `real_entry_conjugate` (`Proofs/RealEntry/ConjScalar`): the antiholomorphic integrand `r⁻³(τ̄-i)^{-k}b̄ⁿ` is the conjugate of the
  holomorphic one, `I̅_n = conj I_n`, and `I̅_n / ((-1)ⁿ(-2i)^{-k}) = 2πi/(n+1) = conj(-2πi/(n+1)) = -c_∞ ≠ 0`.
* `tinf_conjugate_eq_line_seed` (`Proofs/EisensteinClass/LineKBridgeConj`): the conjugate of the real intertwining integral at a
  face point is `2πi/(n+1)` times the conjugate line seed.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.RealEntryConjugate

alias real_entry_conjugate := TernaryPeriodPolynomials.Argument.real_entry_conjugate
alias entry_integral_bar_eq_conj := TernaryPeriodPolynomials.Argument.entryIntegralBar_eq_conj
alias tinf_conjugate_eq_line_seed := TernaryPeriodPolynomials.Argument.EisensteinClass.Tinf_conj_eq_lineSeed

end TernaryPeriodPolynomials.Argument.Statements.RealEntryConjugate
