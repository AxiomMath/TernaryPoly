module

public import TernaryPeriodPolynomials.SymmetricSolution.ScalarGates.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SupportTheorem.OrdinaryReference

@[expose] public section


/-! Target: Proposition 3.4 (`thm:boundary-evaluation`) of the paper. -/

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Proposition 3.4.** If `n > 0`, every `K`-equivariant map `St → E_{n,t}`, `t = 0, 1`
(determinant exponent `e = -t`), takes the identity apartment into `U_n`: its reference value has
two-variable support. -/
theorem support_principle : TernaryPoly.ScalarGates.OrdinaryReferencePairwise := by
  exact TernaryPeriodPolynomials.Argument.Classification.support_principle

end TernaryPeriodPolynomials
