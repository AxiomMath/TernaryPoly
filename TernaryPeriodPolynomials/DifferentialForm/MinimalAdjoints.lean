module

public import TernaryPeriodPolynomials.DifferentialForm.WeakTests
public import TernaryPeriodPolynomials.Analysis.HilbertComplex.AdjointClosure

@[expose] public section


/-! The actual minimal/maximal adjoint identities needed by the analytic exactness criterion. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open scoped LinearPMap

/-- Minimal exterior derivative and maximal codifferential are genuine adjoints. -/
theorem minimalDifferential_adjoint (n k : ℕ) :
    (minimalDifferential n k)† = maximalCodifferential n k :=
  HilbertClosedOperator.adjoint_closure _ (differential_domain_dense n k) (differential_isClosable n k)

/-- Minimal codifferential and maximal exterior derivative are genuine adjoints. -/
theorem minimalCodifferential_adjoint (n k : ℕ) :
    (minimalCodifferential n k)† = maximalDifferential n k :=
  HilbertClosedOperator.adjoint_closure _ (codifferential_domain_dense n k) (codifferential_isClosable n k)

end TernaryPoly.PolynomialFormHilbert
