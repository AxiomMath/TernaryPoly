module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Constructions
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


namespace TernaryPoly.PartialGraphClosed
open Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- The literal graph of a continuous map whose domain is a subtype of X. -/
def graph (U : Set X) (f : U → Y) : Set (X × Y) :=
  {p | ∃ h : p.1 ∈ U, f ⟨p.1,h⟩ = p.2}

/-- If a partial graph has no limit escaping its domain, its graph is closed. -/
theorem isClosed_of_closure_domain (U : Set X) (f : U → Y) (hf : Continuous f)
    (hdom : ∀ p ∈ closure (graph U f), p.1 ∈ U) : IsClosed (graph U f) := by
  let e : U × Y → X × Y := Prod.map Subtype.val id
  let S : Set (U × Y) := {p | f p.1 = p.2}
  have he : IsEmbedding e := IsEmbedding.subtypeVal.prodMap IsEmbedding.id
  have hS : IsClosed S := isClosed_eq (hf.comp continuous_fst) continuous_snd
  have hgraph : e '' S = graph U f := by
    ext p
    constructor
    · rintro ⟨⟨x,y⟩,h,rfl⟩
      exact ⟨x.property,h⟩
    · rintro ⟨h,hf⟩
      exact ⟨(⟨p.1,h⟩,p.2),hf,rfl⟩
  apply isClosed_of_closure_subset
  intro p hp
  have hm : (⟨p.1,hdom p hp⟩,p.2) ∈ e ⁻¹' closure (e '' S) := by
    change p ∈ closure (e '' S)
    rwa [hgraph]
  rw [← he.closure_eq_preimage_closure_image,hS.closure_eq] at hm
  exact ⟨hdom p hp,hm⟩

omit [T2Space Y] in
/-- Continuous invariants retain their equality on every limit of the partial graph. -/
theorem invariants_on_closure [TopologicalSpace Z] [T2Space Z]
    (U : Set X) (f : U → Y) {A : X → Z} {B : Y → Z}
    (hA : Continuous A) (hB : Continuous B)
    (hinv : ∀ x : U, A x.val = B (f x)) :
    ∀ p ∈ closure (graph U f), A p.1 = B p.2 := by
  apply closure_minimal
  · rintro p ⟨h,heq⟩
    exact (hinv ⟨p.1,h⟩).trans (congrArg B heq)
  · exact isClosed_eq (hA.comp continuous_fst) (hB.comp continuous_snd)

/-- Invariant degeneration limits that detect the domain prove a partial graph closed. -/
theorem isClosed_of_invariants [TopologicalSpace Z] [T2Space Z]
    (U : Set X) (f : U → Y) (hf : Continuous f) {A : X → Z} {B : Y → Z}
    (hA : Continuous A) (hB : Continuous B)
    (hinv : ∀ x : U, A x.val = B (f x))
    (hdetect : ∀ x y, A x = B y → x ∈ U) : IsClosed (graph U f) :=
  isClosed_of_closure_domain U f hf fun p hp =>
    hdetect p.1 p.2 (invariants_on_closure U f hA hB hinv p hp)

omit [T2Space Y] in
/-- A dense parameter family has the same graph closure as the whole continuous partial map. -/
theorem closure_dense_graph {T : Type*} (U : Set X) (f : U → Y) (hf : Continuous f)
    (e : T → U) (he : DenseRange e) :
    closure (Set.range (fun t => ((e t).val,f (e t)))) = closure (graph U f) := by
  apply le_antisymm
  · apply closure_mono
    rintro _ ⟨t,rfl⟩
    exact ⟨(e t).property,rfl⟩
  · apply closure_minimal
    · rintro p ⟨h,heq⟩
      let x : U := ⟨p.1,h⟩
      have hm := mem_closure_image (continuous_subtype_val.prodMk hf).continuousAt (he x)
      have hr : (fun x : U => (x.val,f x)) '' Set.range e =
          Set.range (fun t => ((e t).val,f (e t))) := by
        ext z
        simp
      rw [hr] at hm
      simpa only [x,heq,Prod.mk.eta] using hm
    · exact isClosed_closure

end TernaryPoly.PartialGraphClosed
