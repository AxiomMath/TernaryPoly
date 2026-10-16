module

public import TernaryPeriodPolynomials.Analysis.HilbertComplex.MinimalComplex

@[expose] public section


/-! Passing to the minimal graph closure does not change the genuine Hilbert adjoint. -/
namespace TernaryPoly.HilbertClosedOperator
open scoped LinearPMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-- A formal adjoint identity extends continuously across the actual graph closure. -/
theorem formalAdjoint_closure_right (A : F →ₗ.[ℝ] E) (S : E →ₗ.[ℝ] F)
    (hS : S.IsClosable) (h : A.IsFormalAdjoint S) : A.IsFormalAdjoint S.closure := by
  intro a s
  have hc : IsClosed {p : E × F | inner ℝ (A a) p.1 = inner ℝ (a : F) p.2} :=
    isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)
  have hs : (S.graph : Set (E × F)) ⊆ {p : E × F | inner ℝ (A a) p.1 = inner ℝ (a : F) p.2} := by
    intro p hp
    obtain ⟨x, hx, hSx⟩ := S.mem_graph_iff.mp hp
    change inner ℝ (A a) p.1 = inner ℝ (a : F) p.2
    rw [← hx, ← hSx]
    exact h a x
  have hh := closure_minimal hs hc
  apply hh (a := ((s : E), S.closure s))
  rw [← Submodule.topologicalClosure_coe, hS.graph_closure_eq_closure_graph]
  exact S.closure.mem_graph s

/-- Restricting the second operator preserves the exact formal adjoint identity. -/
theorem formalAdjoint_of_le_right (A : F →ₗ.[ℝ] E) (S T : E →ₗ.[ℝ] F)
    (h : A.IsFormalAdjoint T) (hST : S ≤ T) : A.IsFormalAdjoint S := by
  intro a s
  have he := hST.2 (x := s) (y := ⟨(s : E), hST.1 s.property⟩) rfl
  exact (h a ⟨(s : E), hST.1 s.property⟩).trans (congrArg (inner ℝ (a : F)) he.symm)

/-- The adjoint of a closable densely defined operator equals the adjoint of its literal closure. -/
theorem adjoint_closure [CompleteSpace E] (S : E →ₗ.[ℝ] F)
    (hd : Dense (S.domain : Set E)) (hc : S.IsClosable) : S.closure† = S† := by
  apply le_antisymm
  · exact (formalAdjoint_of_le_right S.closure† S S.closure
      (LinearPMap.adjoint_isFormalAdjoint (closure_dense_domain S hd)) S.le_closure).symm.le_adjoint hd
  · exact (formalAdjoint_closure_right S† S hc
      (LinearPMap.adjoint_isFormalAdjoint hd)).symm.le_adjoint (closure_dense_domain S hd)

end TernaryPoly.HilbertClosedOperator
