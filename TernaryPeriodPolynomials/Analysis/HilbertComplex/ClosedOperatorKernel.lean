module

public import Mathlib.Topology.Algebra.Module.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Kernel and orthogonal domain representatives for an actual closed partial operator. -/
namespace TernaryPoly.HilbertClosedOperator

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [NormedSpace ℝ F]

/-- The kernel is a subspace of the ambient Hilbert space, not just of the domain. -/
def kernel (T : E →ₗ.[ℝ] F) : Submodule ℝ E :=
  T.graph.comap ((LinearMap.id : E →ₗ[ℝ] E).prod 0)

@[simp] theorem mem_kernel (T : E →ₗ.[ℝ] F) (x : E) :
    x ∈ kernel T ↔ (x, 0) ∈ T.graph := Iff.rfl

theorem kernel_le_domain (T : E →ₗ.[ℝ] F) : kernel T ≤ T.domain :=
  fun _ h => LinearPMap.mem_domain_of_mem_graph h

@[simp] theorem coe_mem_kernel (T : E →ₗ.[ℝ] F) (x : T.domain) :
    (x : E) ∈ kernel T ↔ T x = 0 := by
  rw [mem_kernel, T.mem_graph_iff]
  constructor
  · rintro ⟨y, hy, hT⟩
    have : y = x := Subtype.ext hy
    simpa [this] using hT
  · exact fun h => ⟨x, rfl, h⟩

theorem kernel_isClosed (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) :
    IsClosed (kernel T : Set E) :=
  hT.preimage (continuous_id.prodMk continuous_const)

/-- Subtracting the genuine kernel projection stays in the unbounded domain and
preserves the image. No closedness of the whole operator domain is assumed. -/
theorem exists_orthogonal_preimage [CompleteSpace E]
    (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : T.domain) :
    ∃ y : T.domain, (y : E) ∈ (kernel T)ᗮ ∧ T y = T x := by
  let : IsClosed (kernel T : Set E) := kernel_isClosed T hT
  let p : T.domain := ⟨(kernel T).starProjection (x : E),
    kernel_le_domain T ((kernel T).starProjection_apply_mem _)⟩
  have hp : T p = 0 := (coe_mem_kernel T p).mp
    ((kernel T).starProjection_apply_mem _)
  refine ⟨x - p, ?_, ?_⟩
  · exact (kernel T).sub_starProjection_mem_orthogonal (x : E)
  · change T.toFun (x - p) = T x
    simp only [map_sub, LinearPMap.toFun_eq_coe, hp, sub_zero]

end TernaryPoly.HilbertClosedOperator
