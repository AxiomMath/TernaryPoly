module

public import TernaryPeriodPolynomials.Analysis.HilbertComplex.ClosedOperatorKernel
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section


/-! Closed-graph recovery from all actual adjoint-domain tests. -/
namespace TernaryPoly.HilbertClosedOperator

open scoped InnerProductSpace LinearPMap
open WithLp
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-- The actual graph equipped with the Hilbert product ambient space. -/
def hilbertGraph (T : E →ₗ.[ℝ] F) : Submodule ℝ (WithLp 2 (E × F)) :=
  T.graph.comap (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap

@[simp] theorem mem_hilbertGraph (T : E →ₗ.[ℝ] F) (x : WithLp 2 (E × F)) :
    x ∈ hilbertGraph T ↔ ofLp x ∈ T.graph := Iff.rfl

theorem hilbertGraph_isClosed (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) :
    IsClosed (hilbertGraph T : Set (WithLp 2 (E × F))) :=
  hT.preimage (WithLp.prod_continuous_ofLp 2 E F)

variable [CompleteSpace E] [CompleteSpace F]

/-- Testing against the genuine adjoint domain recovers membership in the graph
of a closed densely defined operator. This does not assume a double-adjoint identity. -/
theorem mem_graph_of_adjoint_test (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (x : E) (z : F)
    (htest : ∀ y : T†.domain, inner ℝ x (T† y) = inner ℝ z (y : F)) :
    (x, z) ∈ T.graph := by
  let K := hilbertGraph T
  let : IsClosed (K : Set (WithLp 2 (E × F))) := hilbertGraph_isClosed T hT
  have horth : toLp 2 (x, z) ∈ Kᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    have hw' (u : T.domain) :
        inner ℝ (u : E) (ofLp w).1 + inner ℝ (T u) (ofLp w).2 = 0 := by
      have h := (Submodule.mem_orthogonal K w).mp hw (toLp 2 ((u : E), T u))
        (T.mem_graph u)
      simpa only [prod_inner_apply, ofLp_toLp] using h
    have hrepr (u : T.domain) :
        inner ℝ (-(ofLp w).1) (u : E) = inner ℝ (ofLp w).2 (T u) := by
      have h := hw' u
      rw [real_inner_comm (ofLp w).1 (u : E), real_inner_comm (ofLp w).2 (T u)] at h
      rw [inner_neg_left]
      linarith
    have hdw : (ofLp w).2 ∈ T†.domain :=
      T.mem_adjoint_domain_of_exists _ ⟨-(ofLp w).1, hrepr⟩
    have heq : T† ⟨(ofLp w).2, hdw⟩ = -(ofLp w).1 :=
      LinearPMap.adjoint_apply_eq hd _ hrepr
    have h := htest ⟨(ofLp w).2, hdw⟩
    rw [heq, inner_neg_right] at h
    simp only [prod_inner_apply]
    rw [real_inner_comm x (ofLp w).1, real_inner_comm z (ofLp w).2]
    change -inner ℝ x (ofLp w).1 = inner ℝ z (ofLp w).2 at h
    linarith
  rw [K.orthogonal_orthogonal] at horth
  exact horth

end TernaryPoly.HilbertClosedOperator
