module

public import TernaryPeriodPolynomials.DifferentialForm.MaximalComplex
public import TernaryPeriodPolynomials.Analysis.Embedded.AdjointTest

@[expose] public section


/-! The actual maximal form operators are precisely weak differential identities on compact tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open PolynomialCoefficientMetric PolynomialFormCoordinates SmoothCoveringDeRham
open scoped LinearPMap

/-- The maximal differential graph is exactly the identity against all actual compact smooth forms. -/
theorem mem_maximalDifferential_graph_iff (n k : ℕ)
    (x : Hilbert n k) (z : Hilbert n (k + 1)) :
    (x, z) ∈ (maximalDifferential n k).graph ↔
      ∀ b : Core n (k + 1), inner ℝ z (inclusion n (k + 1) b) =
        inner ℝ x (inclusion n k (compactAdjoint n k b)) :=
  EmbeddedLinearOperator.mem_adjoint_graph_iff (inclusion n (k + 1))
    (inclusion_injective n (k + 1)) (inclusion_dense n (k + 1))
    ((inclusion n k).comp (compactAdjoint n k)) x z

/-- The maximal codifferential graph is exactly weak integration by parts against compact tests. -/
theorem mem_maximalCodifferential_graph_iff (n k : ℕ)
    (x : Hilbert n (k + 1)) (z : Hilbert n k) :
    (x, z) ∈ (maximalCodifferential n k).graph ↔
      ∀ b : Core n k, inner ℝ z (inclusion n k b) =
        inner ℝ x (inclusion n (k + 1)
          (compactDifferential (deckRepresentation n) isOpen_univ k b)) :=
  EmbeddedLinearOperator.mem_adjoint_graph_iff (inclusion n k)
    (inclusion_injective n k) (inclusion_dense n k)
    ((inclusion n (k + 1)).comp (compactDifferential (deckRepresentation n) isOpen_univ k)) x z

end TernaryPoly.PolynomialFormHilbert
