module

public import TernaryPeriodPolynomials.DifferentialForm.Differential
public import TernaryPeriodPolynomials.DifferentialForm.GlobalIntegrationByParts

@[expose] public section


/-! Genuine compact-core formal adjoints and closability on the actual form Hilbert completions. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open PolynomialCoefficientMetric PolynomialFormCoordinates SmoothCoveringDeRham
open scoped LinearPMap SymmetricSpaceRiemannian

/-- The actual compact adjoint, embedded with exactly the compact smooth domain. -/
def codifferential (n k : ℕ) : Hilbert n (k + 1) →ₗ.[ℝ] Hilbert n k :=
  EmbeddedLinearOperator.operator (inclusion n (k + 1)) (inclusion_injective n (k + 1))
    ((inclusion n k).comp (compactAdjoint n k))

theorem codifferential_domain (n k : ℕ) :
    ((codifferential n k).domain : Set (Hilbert n (k + 1))) = Set.range (inclusion n (k + 1)) := rfl

theorem codifferential_domain_dense (n k : ℕ) :
    Dense ((codifferential n k).domain : Set (Hilbert n (k + 1))) :=
  EmbeddedLinearOperator.domain_dense _ _ _ (inclusion_dense n (k + 1))

/-- The exact compact adjoint value, without assuming a generic integration-by-parts hypothesis. -/
theorem codifferential_inclusion (n k : ℕ) (a : Core n (k + 1)) :
    codifferential n k ⟨inclusion n (k + 1) a, ⟨a, rfl⟩⟩ = inclusion n k (compactAdjoint n k a) :=
  EmbeddedLinearOperator.operator_apply _ _ _ a

theorem inner_compactDifferential_compactAdjoint (n k : ℕ) (a : Core n k) (b : Core n (k + 1)) :
    inner ℝ (inclusion n (k + 1) (compactDifferential (deckRepresentation n) isOpen_univ k a))
      (inclusion n (k + 1) b) =
    inner ℝ (inclusion n k a) (inclusion n k (compactAdjoint n k b)) := by
  exact (inner_inclusion n (k + 1)
    (compactDifferential (deckRepresentation n) isOpen_univ k a) b).trans
    ((integral_compactDifferential_compactAdjoint n k a b).trans
      (inner_inclusion n k a (compactAdjoint n k b)).symm)

/-- Genuine formal adjointness of the actual compact-core operators. -/
theorem differential_codifferential_formalAdjoint (n k : ℕ) :
    (differential n k).IsFormalAdjoint (codifferential n k) :=
  EmbeddedLinearOperator.isFormalAdjoint (inclusion n k) (inclusion_injective n k)
    (inclusion n (k + 1)) (inclusion_injective n (k + 1))
    (compactDifferential (deckRepresentation n) isOpen_univ k) (compactAdjoint n k)
    (inner_compactDifferential_compactAdjoint n k)

/-- The actual exterior differential is closable in the genuine metric-volume Hilbert completion. -/
theorem differential_isClosable (n k : ℕ) : (differential n k).IsClosable :=
  HilbertClosedOperator.isClosable_of_formalAdjoint _ _ (codifferential_domain_dense n k)
    (differential_codifferential_formalAdjoint n k)

/-- The actual compact adjoint is closable as well. -/
theorem codifferential_isClosable (n k : ℕ) : (codifferential n k).IsClosable :=
  HilbertClosedOperator.isClosable_of_formalAdjoint _ _ (differential_domain_dense n k)
    (differential_codifferential_formalAdjoint n k).symm

end TernaryPoly.PolynomialFormHilbert
