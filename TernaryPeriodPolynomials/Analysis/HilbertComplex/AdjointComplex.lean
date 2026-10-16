module

public import TernaryPeriodPolynomials.Analysis.HilbertComplex.ClosedOperatorKernel
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section

/-! Adjoint complexes, using the actual densely defined operator domains. -/
namespace TernaryPoly.HilbertClosedOperator
open scoped InnerProductSpace LinearPMap
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [InnerProductSpace ℝ G]
  [CompleteSpace E] [CompleteSpace F]

/-- The adjoints reverse a densely defined complex, with genuine adjoint-domain membership. -/
theorem adjoint_complex (S : E →ₗ.[ℝ] F) (T : F →ₗ.[ℝ] G)
    (hdS : Dense (S.domain : Set E)) (hdT : Dense (T.domain : Set F))
    (hC : ∀ u : S.domain, S u ∈ kernel T) (v : T†.domain) :
    T† v ∈ kernel S† := by
  have ht (u : S.domain) : inner ℝ (0 : E) (u : E) = inner ℝ (T† v) (S u) := by
    have hu := hC u
    rw [mem_kernel] at hu
    obtain ⟨w, hw, hzero⟩ := T.mem_graph_iff.mp hu
    change (w : F) = S u at hw
    change T w = 0 at hzero
    rw [← hw, LinearPMap.adjoint_isFormalAdjoint hdT v w, hzero]
    simp
  have hv : T† v ∈ S†.domain := S.mem_adjoint_domain_of_exists _ ⟨0, ht⟩
  have heq : S† ⟨T† v, hv⟩ = 0 := LinearPMap.adjoint_apply_eq hdS _ ht
  exact (mem_kernel S† _).mpr (heq ▸ S†.mem_graph ⟨T† v, hv⟩)

end TernaryPoly.HilbertClosedOperator
