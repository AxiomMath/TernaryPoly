module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section

namespace TernaryPoly.CompactDenseImage

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space Y]

/-- Compact representatives that contain a dense family cover the whole Hausdorff target. -/
theorem image_eq_univ {K : Set X} (hK : IsCompact K) {k : X → Y} (hk : Continuous k)
    {d : Z → Y} (hd : DenseRange d) (hcover : Set.range d ⊆ k '' K) :
    k '' K = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← hd.closure_range]
  exact closure_minimal hcover (hK.image hk).isClosed

/-- This criterion promotes compact representatives of a dense locus to compactness. -/
theorem compactSpace {K : Set X} (hK : IsCompact K) {k : X → Y} (hk : Continuous k)
    {d : Z → Y} (hd : DenseRange d) (hcover : Set.range d ⊆ k '' K) : CompactSpace Y := by
  constructor
  rw [← image_eq_univ hK hk hd hcover]
  exact hK.image hk

end TernaryPoly.CompactDenseImage
