module

public import TernaryPeriodPolynomials.Analysis.HilbertComplex.ClosedOperatorAdjointTest
public import TernaryPeriodPolynomials.Analysis.HilbertComplex.BoundedFunctionalFactor

@[expose] public section


/-! A genuine preimage criterion for closed, densely defined Hilbert-space operators. -/
namespace TernaryPoly.HilbertClosedOperator

open scoped InnerProductSpace LinearPMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
variable [CompleteSpace E] [CompleteSpace F]

/-- An estimate against all adjoint-domain test vectors produces an actual
preimage, not just an element of the closure of the range. -/
theorem mem_range_of_adjoint_bound (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (z : F) (C : ℝ)
    (hb : ∀ y : T†.domain, ‖inner ℝ z (y : F)‖ ≤ C * ‖T† y‖) :
    z ∈ Set.range T := by
  let φ : T†.domain →ₗ[ℝ] ℝ := (innerₛₗ ℝ z).comp T†.domain.subtype
  obtain ⟨x, hx⟩ := HilbertBoundedFunctional.exists_inner_factor T†.toFun φ C hb
  exact LinearPMap.mem_range_iff.mpr ⟨x, mem_graph_of_adjoint_test T hT hd x z hx⟩

end TernaryPoly.HilbertClosedOperator
