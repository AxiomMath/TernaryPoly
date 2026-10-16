module

public import TernaryPeriodPolynomials.DifferentialForm.CodifferentialComplex
public import TernaryPeriodPolynomials.Analysis.HilbertComplex.AdjointComplex
public import TernaryPeriodPolynomials.Analysis.HilbertComplex.ClosedExtension

@[expose] public section


/-! Actual maximal differential and codifferential complexes, defined by compact-core tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open scoped LinearPMap

/-- The maximal weak exterior differential, tested against the actual compact codifferential. -/
def maximalDifferential (n k : ℕ) : Hilbert n k →ₗ.[ℝ] Hilbert n (k + 1) :=
  (codifferential n k)†

/-- The maximal weak codifferential, tested against the actual compact differential. -/
def maximalCodifferential (n k : ℕ) : Hilbert n (k + 1) →ₗ.[ℝ] Hilbert n k :=
  (differential n k)†

theorem maximalDifferential_isClosed (n k : ℕ) : (maximalDifferential n k).IsClosed :=
  LinearPMap.adjoint_isClosed (codifferential_domain_dense n k)

theorem maximalCodifferential_isClosed (n k : ℕ) : (maximalCodifferential n k).IsClosed :=
  LinearPMap.adjoint_isClosed (differential_domain_dense n k)

theorem differential_le_maximal (n k : ℕ) : differential n k ≤ maximalDifferential n k :=
  (differential_codifferential_formalAdjoint n k).symm.le_adjoint (codifferential_domain_dense n k)

theorem codifferential_le_maximal (n k : ℕ) : codifferential n k ≤ maximalCodifferential n k :=
  (differential_codifferential_formalAdjoint n k).le_adjoint (differential_domain_dense n k)

theorem maximalDifferential_domain_dense (n k : ℕ) :
    Dense ((maximalDifferential n k).domain : Set (Hilbert n k)) :=
  (differential_domain_dense n k).mono (differential_le_maximal n k).1

theorem maximalCodifferential_domain_dense (n k : ℕ) :
    Dense ((maximalCodifferential n k).domain : Set (Hilbert n (k + 1))) :=
  (codifferential_domain_dense n k).mono (codifferential_le_maximal n k).1

/-- Genuine inclusion only: equality requires a separate approximation theorem. -/
theorem minimalDifferential_le_maximal (n k : ℕ) :
    minimalDifferential n k ≤ maximalDifferential n k :=
  HilbertClosedOperator.closure_le _ _ (maximalDifferential_isClosed n k)
    (differential_le_maximal n k)

theorem minimalCodifferential_le_maximal (n k : ℕ) :
    minimalCodifferential n k ≤ maximalCodifferential n k :=
  HilbertClosedOperator.closure_le _ _ (maximalCodifferential_isClosed n k)
    (codifferential_le_maximal n k)

/-- The weak differential squares to zero on its full actual maximal domain. -/
theorem maximalDifferential_complex (n k : ℕ) (a : (maximalDifferential n k).domain) :
    maximalDifferential n k a ∈ HilbertClosedOperator.kernel (maximalDifferential n (k + 1)) :=
  HilbertClosedOperator.adjoint_complex (codifferential n (k + 1)) (codifferential n k)
    (codifferential_domain_dense n (k + 1)) (codifferential_domain_dense n k)
    (codifferential_complex n k) a

/-- The weak codifferential also forms the reversed complex on its full domain. -/
theorem maximalCodifferential_complex (n k : ℕ) (a : (maximalCodifferential n (k + 1)).domain) :
    maximalCodifferential n (k + 1) a ∈ HilbertClosedOperator.kernel (maximalCodifferential n k) :=
  HilbertClosedOperator.adjoint_complex (differential n k) (differential n (k + 1))
    (differential_domain_dense n k) (differential_domain_dense n (k + 1))
    (differential_complex n k) a

end TernaryPoly.PolynomialFormHilbert
