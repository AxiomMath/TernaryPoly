module

public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Basic
public import TernaryPeriodPolynomials.Analysis.Embedded.LinearComplex

@[expose] public section


/-! The actual densely defined exterior differential on the genuine form Hilbert spaces. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open PolynomialCoefficientMetric SmoothCoveringDeRham
open scoped LinearPMap

/-- The prescribed compact smooth exterior derivative in the genuine Hilbert completion. -/
def differential (n k : ℕ) : Hilbert n k →ₗ.[ℝ] Hilbert n (k + 1) :=
  EmbeddedLinearOperator.operator (inclusion n k) (inclusion_injective n k)
    ((inclusion n (k + 1)).comp (compactDifferential (deckRepresentation n) isOpen_univ k))

/-- The domain consists exactly of the embedded actual compact smooth forms. -/
theorem differential_domain (n k : ℕ) : (differential n k).domain = (inclusion n k).range := rfl

theorem differential_domain_dense (n k : ℕ) : Dense ((differential n k).domain : Set (Hilbert n k)) :=
  EmbeddedLinearOperator.domain_dense _ _ _ (inclusion_dense n k)

/-- This identifies its value with the literal existing exterior derivative. -/
theorem differential_inclusion (n k : ℕ) (a : Core n k) :
    differential n k ⟨inclusion n k a, ⟨a, rfl⟩⟩ =
      inclusion n (k + 1) (compactDifferential (deckRepresentation n) isOpen_univ k a) :=
  EmbeddedLinearOperator.operator_apply _ _ _ a

/-- The actual operators satisfy the exterior-complex law on their actual domains. -/
theorem differential_complex (n k : ℕ) (a : (differential n k).domain) :
    differential n k a ∈ HilbertClosedOperator.kernel (differential n (k + 1)) :=
  EmbeddedLinearOperator.complex (inclusion n k) (inclusion_injective n k)
    (inclusion n (k + 1)) (inclusion_injective n (k + 1)) (inclusion n (k + 1 + 1))
    (compactDifferential (deckRepresentation n) isOpen_univ k)
    (compactDifferential (deckRepresentation n) isOpen_univ (k + 1))
    (compactDifferential_squared (deckRepresentation n) isOpen_univ k) a

end TernaryPoly.PolynomialFormHilbert
