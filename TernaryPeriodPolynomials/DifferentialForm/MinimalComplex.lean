module

public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Adjoint

@[expose] public section

/-! The actual minimal closed exterior complex in the genuine form Hilbert completions. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open scoped LinearPMap

/-- Closure of the literal compact smooth exterior differential. -/
def minimalDifferential (n k : ℕ) : Hilbert n k →ₗ.[ℝ] Hilbert n (k + 1) :=
  (differential n k).closure

/-- Closure of the literal compact smooth codifferential. -/
def minimalCodifferential (n k : ℕ) : Hilbert n (k + 1) →ₗ.[ℝ] Hilbert n k :=
  (codifferential n k).closure

theorem minimalDifferential_isClosed (n k : ℕ) : (minimalDifferential n k).IsClosed :=
  (differential_isClosable n k).closure_isClosed

theorem minimalCodifferential_isClosed (n k : ℕ) : (minimalCodifferential n k).IsClosed :=
  (codifferential_isClosable n k).closure_isClosed

theorem minimalDifferential_domain_dense (n k : ℕ) :
    Dense ((minimalDifferential n k).domain : Set (Hilbert n k)) :=
  HilbertClosedOperator.closure_dense_domain _ (differential_domain_dense n k)

theorem minimalCodifferential_domain_dense (n k : ℕ) :
    Dense ((minimalCodifferential n k).domain : Set (Hilbert n (k + 1))) :=
  HilbertClosedOperator.closure_dense_domain _ (codifferential_domain_dense n k)

/-- The actual minimal closures retain the genuine exterior-complex law. -/
theorem minimalDifferential_complex (n k : ℕ) (a : (minimalDifferential n k).domain) :
    minimalDifferential n k a ∈ HilbertClosedOperator.kernel (minimalDifferential n (k + 1)) :=
  HilbertClosedOperator.closure_complex _ _ (differential_isClosable n k)
    (differential_isClosable n (k + 1)) (differential_complex n k) a

end TernaryPoly.PolynomialFormHilbert
