module

public import TernaryPeriodPolynomials.Analysis.HilbertComplex.ComplexEnergy

@[expose] public section


/-! An actual graph-form energy estimate supplies exactness with a named genuine adjoint. -/
namespace TernaryPoly.HilbertClosedOperator
open scoped LinearPMap
variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [NormedSpace ℝ G]
  [CompleteSpace E] [CompleteSpace F]

theorem exact_of_graph_energy (S : E →ₗ.[ℝ] F) (T : F →ₗ.[ℝ] G) (U : F →ₗ.[ℝ] E)
    (hS : S.IsClosed) (hdS : Dense (S.domain : Set E)) (hT : T.IsClosed)
    (hcomplex : ∀ u : S.domain, S u ∈ kernel T) (hU : S.adjoint = U)
    (c : ℝ) (hc : 0 < c)
    (henergy : ∀ (x : F) (y : G) (z : E), (x,y) ∈ T.graph → (x,z) ∈ U.graph →
      c * ‖x‖^2 ≤ ‖z‖^2 + ‖y‖^2) :
    (kernel T : Set F) = Set.range S := by
  apply exact_of_energy S T hS hdS hT hcomplex c hc
  intro x hx
  have hu : ((x : F), S.adjoint ⟨(x : F),hx⟩) ∈ U.graph := by
    rw [← hU]
    exact S.adjoint.mem_graph ⟨(x : F),hx⟩
  exact (henergy x (T x) (S.adjoint ⟨(x : F),hx⟩) (T.mem_graph x) hu).trans_eq (add_comm _ _)

end TernaryPoly.HilbertClosedOperator
