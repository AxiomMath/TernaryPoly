module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Action.Pointwise.Set
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
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Compact subsets of real convex open sets have interior interval bounds. -/
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set

/-- Every nonempty compact subset of a real convex open set lies strictly between two
points whose entire closed interval remains in that open set. -/
theorem compact_subset_open_convex_interval {K Ω : Set ℝ} (hK : IsCompact K)
    (hn : K.Nonempty) (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hs : K ⊆ Ω) :
    ∃ a b : ℝ, K ⊆ Ioo a b ∧ Icc a b ⊆ Ω := by
  obtain ⟨l, hl⟩ := hK.exists_isLeast hn
  obtain ⟨r, hr⟩ := hK.exists_isGreatest hn
  obtain ⟨a, a', hla, ha⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hΩ.mem_nhds (hs hl.1))
  obtain ⟨b', b, hrb, hb⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hΩ.mem_nhds (hs hr.1))
  have hal : (a + l) / 2 < l := by linarith [hla.1]
  have hrbb : r < (r + b) / 2 := by linarith [hrb.2]
  have haΩ : (a + l) / 2 ∈ Ω := ha ⟨by linarith [hla.1], by linarith [hla.1, hla.2]⟩
  have hbΩ : (r + b) / 2 ∈ Ω := hb ⟨by linarith [hrb.1, hrb.2], by linarith [hrb.2]⟩
  refine ⟨(a + l) / 2, (r + b) / 2, ?_, hc.ordConnected.out haΩ hbΩ⟩
  intro x hx
  exact ⟨hal.trans_le (hl.2 hx), (hr.2 hx).trans_lt hrbb⟩

end TernaryPoly.PolynomialFormWeakSmooth
