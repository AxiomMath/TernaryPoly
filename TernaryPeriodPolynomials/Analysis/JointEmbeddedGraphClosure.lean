module

public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Hom.InjSurj
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
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! The closure of actual simultaneous triples from one linear core. -/
namespace TernaryPoly.JointEmbeddedGraphClosure
open Set Filter
open scoped Topology
variable {V E F G : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def graph (i : V →ₗ[ℝ] E) (d : V →ₗ[ℝ] F) (a : V →ₗ[ℝ] G) :
    Submodule ℝ (E × F × G) :=
  (LinearMap.range (i.prod (d.prod a))).topologicalClosure

theorem mem_of_sequence (i : V →ₗ[ℝ] E) (d : V →ₗ[ℝ] F) (a : V →ₗ[ℝ] G)
    (u : ℕ → V) (x : E) (y : F) (z : G)
    (hx : Tendsto (fun j => i (u j)) atTop (𝓝 x))
    (hy : Tendsto (fun j => d (u j)) atTop (𝓝 y))
    (hz : Tendsto (fun j => a (u j)) atTop (𝓝 z)) :
    (x,y,z) ∈ graph i d a := by
  apply (LinearMap.range (i.prod (d.prod a))).isClosed_topologicalClosure.mem_of_tendsto
    (hx.prodMk_nhds (hy.prodMk_nhds hz))
  exact Eventually.of_forall (fun j =>
    (LinearMap.range (i.prod (d.prod a))).le_topologicalClosure ⟨u j,rfl⟩)

theorem exists_sequence (i : V →ₗ[ℝ] E) (d : V →ₗ[ℝ] F) (a : V →ₗ[ℝ] G)
    {x : E} {y : F} {z : G} (h : (x,y,z) ∈ graph i d a) :
    ∃ u : ℕ → V, Tendsto (fun j => i (u j)) atTop (𝓝 x) ∧
      Tendsto (fun j => d (u j)) atTop (𝓝 y) ∧ Tendsto (fun j => a (u j)) atTop (𝓝 z) := by
  obtain ⟨v,hv,ht⟩ := mem_closure_iff_seq_limit.mp h
  choose u hu using hv
  have he : Tendsto (fun j => (i (u j),d (u j),a (u j))) atTop (𝓝 (x,y,z)) := by
    exact ht.congr (fun j => (hu j).symm)
  exact ⟨u,he.fst_nhds,he.snd_nhds.fst_nhds,he.snd_nhds.snd_nhds⟩

theorem mem_of_limits (i : V →ₗ[ℝ] E) (d : V →ₗ[ℝ] F) (a : V →ₗ[ℝ] G)
    (u : ℕ → E) (v : ℕ → F) (w : ℕ → G)
    (h : ∀ j, (u j,v j,w j) ∈ graph i d a) (x : E) (y : F) (z : G)
    (hx : Tendsto u atTop (𝓝 x)) (hy : Tendsto v atTop (𝓝 y)) (hz : Tendsto w atTop (𝓝 z)) :
    (x,y,z) ∈ graph i d a :=
  (LinearMap.range (i.prod (d.prod a))).isClosed_topologicalClosure.mem_of_tendsto
    (hx.prodMk_nhds (hy.prodMk_nhds hz)) (Eventually.of_forall h)

end TernaryPoly.JointEmbeddedGraphClosure
