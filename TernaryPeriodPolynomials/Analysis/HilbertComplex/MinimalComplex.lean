module

public import TernaryPeriodPolynomials.Analysis.HilbertComplex.ClosedOperatorKernel
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section


/-! Closable differential pairs and their actual minimal closed extensions. -/
namespace TernaryPoly.HilbertClosedOperator

open scoped InnerProductSpace LinearPMap
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [NormedSpace ℝ G]

/-- A densely defined formal adjoint supplies a genuine closed extension. -/
theorem isClosable_of_formalAdjoint [CompleteSpace F]
    (S : E →ₗ.[ℝ] F) (A : F →ₗ.[ℝ] E)
    (hA : Dense (A.domain : Set F)) (h : S.IsFormalAdjoint A) : S.IsClosable := by
  exact LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨A†, LinearPMap.adjoint_isClosed hA, h.symm.le_adjoint hA⟩

/-- Closure retains density of an actual initial operator domain. -/
theorem closure_dense_domain (S : E →ₗ.[ℝ] F) (hd : Dense (S.domain : Set E)) :
    Dense (S.closure.domain : Set E) :=
  hd.mono S.le_closure.1

/-- If the initial consecutive differentials form a complex, their actual
minimal closures do too. The proof uses their graph closures, not pointwise
continuity of the unbounded operators. -/
theorem closure_complex (S : E →ₗ.[ℝ] F) (T : F →ₗ.[ℝ] G)
    (hS : S.IsClosable) (hT : T.IsClosable)
    (hcomplex : ∀ u : S.domain, S u ∈ kernel T) :
    ∀ u : S.closure.domain, S.closure u ∈ kernel T.closure := by
  have hclosed : IsClosed {p : E × F | (p.2, (0 : G)) ∈ T.closure.graph} :=
    hT.closure_isClosed.preimage (continuous_snd.prodMk continuous_const)
  have hsubset : (S.graph : Set (E × F)) ⊆ {p : E × F | (p.2, (0 : G)) ∈ T.closure.graph} := by
    intro p hp
    obtain ⟨u, _, hu⟩ := S.mem_graph_iff.mp hp
    have h := hcomplex u
    rw [mem_kernel] at h
    exact LinearPMap.le_graph_of_le T.le_closure (hu ▸ h)
  have hclosure := closure_minimal hsubset hclosed
  intro u
  change (S.closure u, (0 : G)) ∈ T.closure.graph
  apply hclosure (a := ((u : E), S.closure u))
  rw [← Submodule.topologicalClosure_coe, hS.graph_closure_eq_closure_graph]
  exact S.closure.mem_graph u

end TernaryPoly.HilbertClosedOperator
