module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Maps.Basic
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


noncomputable section
namespace TernaryPoly.CompactEmbeddingNeighborhood
open Set Topology

/-- A continuous map to a Hausdorff space that is injective on a compact subset and locally
injective near each point of that subset is injective on a single open neighborhood. -/
theorem exists_open_injOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (S : Set X) (hS : IsCompact S) (hinj : Set.InjOn f S)
    (hloc : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U) :
    ∃ U : Set X, IsOpen U ∧ S ⊆ U ∧ Set.InjOn f U := by
  let R : Set (X × X) := {z | f z.1 = f z.2 → z.1 = z.2}
  have hnear : S ×ˢ S ⊆ interior R := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    by_cases hxy : x = y
    · subst y
      obtain ⟨U, hU, hxU, hUinj⟩ := hloc x hx
      apply mem_interior.mpr
      refine ⟨U ×ˢ U, ?_, hU.prod hU, ⟨hxU, hxU⟩⟩
      rintro ⟨u, v⟩ ⟨hu, hv⟩ huv
      exact hUinj hu hv huv
    · have hneq : f x ≠ f y := fun h => hxy (hinj hx hy h)
      apply mem_interior.mpr
      refine ⟨{z : X × X | f z.1 ≠ f z.2}, ?_,
        (isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd)).isOpen_compl, hneq⟩
      intro z hz he
      exact (hz he).elim
  obtain ⟨U, V, hU, hV, hSU, hSV, hUV⟩ :=
    generalized_tube_lemma hS hS isOpen_interior hnear
  refine ⟨U ∩ V, hU.inter hV, fun x hx => ⟨hSU hx, hSV hx⟩, ?_⟩
  intro x hx y hy hxy
  have h : (x, y) ∈ R := interior_subset (hUV ⟨hx.1, hy.2⟩)
  exact h hxy

/-- For an open continuous map, local injectivity along a compact embedded subset gives a
single actual open-embedding neighborhood of that subset. -/
theorem exists_open_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] (f : X → Y) (hf : Continuous f) (hopen : IsOpenMap f)
    (S : Set X) (hS : IsCompact S) (hinj : Set.InjOn f S)
    (hloc : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U) :
    ∃ U : Set X, IsOpen U ∧ S ⊆ U ∧ IsOpenEmbedding (U.domRestrict f) := by
  obtain ⟨U, hU, hSU, hUi⟩ := exists_open_injOn f hf S hS hinj hloc
  refine ⟨U, hU, hSU, ?_⟩
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hf.comp continuous_subtype_val) hUi.injective (hopen.domRestrict hU)

end TernaryPoly.CompactEmbeddingNeighborhood
