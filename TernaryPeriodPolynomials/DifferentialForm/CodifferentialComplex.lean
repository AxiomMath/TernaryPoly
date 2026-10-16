module

public import TernaryPeriodPolynomials.DifferentialForm.MinimalComplex
public import TernaryPeriodPolynomials.Analysis.Embedded.AdjointComplex

@[expose] public section


/-! The actual compact and minimal codifferentials form the reversed exterior complex. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open PolynomialCoefficientMetric PolynomialFormCoordinates SmoothCoveringDeRham
open scoped LinearPMap SymmetricSpaceRiemannian

/-- The genuine compact smooth adjoint squares to zero, by actual adjointness and d²=0. -/
theorem compactAdjoint_squared (n k : ℕ) (a : Core n (k + 1 + 1)) :
    compactAdjoint n k (compactAdjoint n (k + 1) a) = 0 :=
  EmbeddedLinearOperator.adjoint_comp_eq_zero (inclusion n k) (inclusion_injective n k)
    (inclusion n (k + 1)) (inclusion n (k + 1 + 1))
    (compactDifferential (deckRepresentation n) isOpen_univ k)
    (compactDifferential (deckRepresentation n) isOpen_univ (k + 1))
    (compactAdjoint n k) (compactAdjoint n (k + 1))
    (inner_compactDifferential_compactAdjoint n k)
    (inner_compactDifferential_compactAdjoint n (k + 1))
    (compactDifferential_squared (deckRepresentation n) isOpen_univ k) a

/-- Consecutive actual compact-core codifferentials form a complex. -/
theorem codifferential_complex (n k : ℕ) (a : (codifferential n (k + 1)).domain) :
    codifferential n (k + 1) a ∈ HilbertClosedOperator.kernel (codifferential n k) :=
  EmbeddedLinearOperator.complex (E := Hilbert n (k + 1 + 1))
    (F := Hilbert n (k + 1)) (G := Hilbert n k) (inclusion n (k + 1 + 1)) (inclusion_injective n (k + 1 + 1))
    (inclusion n (k + 1)) (inclusion_injective n (k + 1)) (inclusion n k)
    (compactAdjoint n (k + 1)) (compactAdjoint n k) (compactAdjoint_squared n k) a

/-- The genuine minimal closures retain the reversed complex law. -/
theorem minimalCodifferential_complex (n k : ℕ) (a : (minimalCodifferential n (k + 1)).domain) :
    minimalCodifferential n (k + 1) a ∈ HilbertClosedOperator.kernel (minimalCodifferential n k) :=
  HilbertClosedOperator.closure_complex (E := Hilbert n (k + 1 + 1))
    (F := Hilbert n (k + 1)) (G := Hilbert n k) _ _ (codifferential_isClosable n (k + 1))
    (codifferential_isClosable n k) (codifferential_complex n k) a

end TernaryPoly.PolynomialFormHilbert
