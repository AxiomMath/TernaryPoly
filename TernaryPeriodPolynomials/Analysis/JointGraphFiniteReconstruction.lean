module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
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
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Finite reconstruction of values determines the derivative coordinates in a joint graph submodule. -/
namespace TernaryPoly.JointGraphFiniteReconstruction
open scoped LinearPMap
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

theorem graph_value_unique (T : E →ₗ.[ℝ] F) {x : E} {y z : F}
    (hy : (x,y) ∈ T.graph) (hz : (x,z) ∈ T.graph) : y = z := by
  obtain ⟨a,ha,hay⟩ := T.mem_graph_iff.mp hy
  obtain ⟨b,hb,hbz⟩ := T.mem_graph_iff.mp hz
  exact hay.symm.trans ((congrArg T (Subtype.ext (ha.trans hb.symm))).trans hbz)

theorem mem_of_finite_reconstruction {I : Type*} [Fintype I]
    (J : Submodule ℝ (E × F × G)) (T : E →ₗ.[ℝ] F) (U : E →ₗ.[ℝ] G)
    (hJ : ∀ x y z, (x,y,z) ∈ J → (x,y) ∈ T.graph ∧ (x,z) ∈ U.graph)
    (f : I → E) (x : E) (y : F) (z : G)
    (hf : ∀ i, ∃ v : F, ∃ w : G, (f i,v,w) ∈ J)
    (hs : ∑ i, f i = x) (hy : (x,y) ∈ T.graph) (hz : (x,z) ∈ U.graph) :
    (x,y,z) ∈ J := by
  choose v w hvw using hf
  let t : E × F × G := ∑ i, (f i,v i,w i)
  have ht : t ∈ J := J.sum_mem (fun i _ => hvw i)
  have hx : t.1 = x := by simpa only [t, Prod.fst_sum] using hs
  have h0 : (x,t.2.1,t.2.2) ∈ J := by simpa only [← hx, Prod.mk.eta] using ht
  have h1 := hJ x t.2.1 t.2.2 h0
  have h2 := graph_value_unique T h1.1 hy
  have h3 := graph_value_unique U h1.2 hz
  exact (congrArg₂ (fun y z => (x,y,z) ∈ J) h2 h3).mp h0

end TernaryPoly.JointGraphFiniteReconstruction
