module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.Fintype.Option
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


noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open TopologicalSpace
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

/-- Every point-indexed open cover of a compact set admits finitely many compact pieces inside the original set and subordinate to the prescribed neighborhoods. -/
theorem finite_compact_refinement (K : Set X) (hK : IsCompact K) (U : K → Opens X)
    (hU : ∀ x : K, x.val ∈ U x) :
    ∃ (s : Finset K) (L : K → Set X),
      (∀ x ∈ s, IsCompact (L x)) ∧ (∀ x ∈ s, L x ⊆ K) ∧
      (∀ x ∈ s, L x ⊆ U x) ∧ (⋃ x ∈ s, L x) = K := by
  classical
  choose C hCc hxC hCU using fun x : K => exists_compact_subset (U x).isOpen (hU x)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => interior (C x))
    (fun _ => isOpen_interior) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x,hx⟩, hxC ⟨x,hx⟩⟩)
  refine ⟨s, fun x => K ∩ C x, fun x _ => hK.inter (hCc x), fun _ _ => Set.inter_subset_left,
    fun x _ => Set.inter_subset_right.trans (hCU x), ?_⟩
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun _ _ => Set.inter_subset_left
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion₂.mpr ⟨y, hy, hx, interior_subset hxy⟩

end TernaryPoly.RationalManifoldCompact
