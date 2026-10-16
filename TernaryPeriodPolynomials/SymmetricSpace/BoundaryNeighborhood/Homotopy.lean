module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Compactness.Compact
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
namespace TernaryPoly.BoundaryNeighborhood
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] {A W : Set X}

/-- A deformation fixing the boundary pointwise and preserving a prescribed neighborhood. -/
structure Deformation (A W : Set X) where
  homotopy : C(I × X, X)
  zero : ∀ x, homotopy (0,x) = x
  fixes : ∀ t x, x ∈ A → homotopy (t,x) = x
  preserves : ∀ t x, x ∈ W → homotopy (t,x) ∈ W

/-- The identity deformation provides the empty finite composition. -/
def Deformation.identity (A W : Set X) : Deformation A W where
  homotopy := ContinuousMap.snd
  zero _ := rfl
  fixes _ _ _ := rfl
  preserves _ _ hx := hx

/-- Finite composition preserves the actual pointwise boundary and neighborhood conditions. -/
def Deformation.comp (d e : Deformation A W) : Deformation A W where
  homotopy := ⟨fun p => d.homotopy (p.1,e.homotopy p),
    d.homotopy.continuous.comp (continuous_fst.prodMk e.homotopy.continuous)⟩
  zero x := by simp only [ContinuousMap.coe_mk,e.zero,d.zero]
  fixes t x hx := by
    change d.homotopy (t,e.homotopy (t,x)) = x
    rw [e.fixes t x hx,d.fixes t x hx]
  preserves t x hx := d.preserves t _ (e.preserves t x hx)

/-- Simultaneous-parameter composition of a finite list of boundary-fixing deformations. -/
def combine : List (Deformation A W) → Deformation A W
  | [] => .identity A W
  | d::l => d.comp (combine l)

/-- A local time-one collapse remains a local collapse after any finite composition containing it.
The neighborhood is pulled back through preceding endpoint maps, which fix the boundary point. -/
theorem combine_locally (l : List (Deformation A W)) (d : Deformation A W) (hd : d ∈ l)
    (x : X) (hx : x ∈ A) (V : Set X) (hV : IsOpen V) (hxV : x ∈ V)
    (hVA : ∀ y ∈ V, d.homotopy (1,y) ∈ A) :
    ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∀ y ∈ N, (combine l).homotopy (1,y) ∈ A := by
  induction l with
  | nil => simp at hd
  | cons e l ih =>
    rcases List.mem_cons.mp hd with he | hd
    · subst e
      let f : C(X,X) := ⟨fun y => (combine l).homotopy (1,y),
        (combine l).homotopy.continuous.comp (continuous_const.prodMk continuous_id)⟩
      refine ⟨f ⁻¹' V,hV.preimage f.continuous,?_,?_⟩
      · change (combine l).homotopy (1,x) ∈ V
        rw [(combine l).fixes 1 x hx]
        exact hxV
      · intro y hy
        exact hVA (f y) hy
    · obtain ⟨N,hN,hxN,hNA⟩ := ih hd
      refine ⟨N,hN,hxN,?_⟩
      intro y hy
      change e.homotopy (1,(combine l).homotopy (1,y)) ∈ A
      rw [e.fixes 1 _ (hNA y hy)]
      exact hNA y hy

/-- Compactness assembles actual local boundary collapses into a global boundary-fixing
homotopy that collapses some smaller open neighborhood into the boundary. It preserves the
prescribed larger neighborhood throughout; no global product collar is assumed. -/
theorem exists_global (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W)
    (hlocal : ∀ x ∈ A, ∃ d : Deformation A W, ∃ V : Set X,
      IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, d.homotopy (1,y) ∈ A) :
    ∃ d : Deformation A W, ∃ N : Set X, IsOpen N ∧ A ⊆ N ∧ N ⊆ W ∧
      ∀ y ∈ N, d.homotopy (1,y) ∈ A := by
  classical
  choose d V hV hxV hVA using fun x : A => hlocal x.val x.property
  have hcover : A ⊆ ⋃ x : A, V x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  obtain ⟨t,ht⟩ := hA.elim_finite_subcover V hV hcover
  let l := t.toList.map d
  have hnear (x : A) : ∃ N : Set X, IsOpen N ∧ x.val ∈ N ∧
      ∀ y ∈ N, (combine l).homotopy (1,y) ∈ A := by
    obtain ⟨z,hz,hxz⟩ := Set.mem_iUnion₂.mp (ht x.property)
    exact combine_locally l (d z) (List.mem_map.mpr ⟨z,Finset.mem_toList.mpr hz,rfl⟩)
      x.val x.property (V z) (hV z) hxz (hVA z)
  choose N hN hxN hNA using hnear
  refine ⟨combine l, W ∩ ⋃ x : A, N x, hW.inter (isOpen_iUnion hN),?_,Set.inter_subset_left,?_⟩
  · intro x hx
    exact ⟨hAW hx,Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hxN ⟨x,hx⟩⟩⟩
  · intro y hy
    obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hy.2
    exact hNA x y hx

/-- A smaller-neighborhood collapse supplies the literal continuous map to the boundary. -/
def endpointRetraction (d : Deformation A W) (N : Set X)
    (hNA : ∀ y ∈ N, d.homotopy (1,y) ∈ A) : C(N,A) :=
  ⟨fun y => ⟨d.homotopy (1,y.val),hNA y.val y.property⟩,
    (d.homotopy.continuous.comp (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩

/-- The collapse fixes each actual boundary point in the smaller neighborhood. -/
theorem endpointRetraction_boundary (d : Deformation A W) (N : Set X)
    (hAN : A ⊆ N) (hNA : ∀ y ∈ N, d.homotopy (1,y) ∈ A) (x : A) :
    endpointRetraction d N hNA ⟨x.val,hAN x.property⟩ = x :=
  Subtype.ext (d.fixes 1 x.val x.property)

/-- The inclusion of the smaller neighborhood in the larger one is genuinely homotopic
inside the larger neighborhood to the actual map factoring through the boundary. -/
def endpointHomotopy (d : Deformation A W) (N : Set X) (hNW : N ⊆ W) (hAW : A ⊆ W)
    (hNA : ∀ y ∈ N, d.homotopy (1,y) ∈ A) :
    ContinuousMap.Homotopy
      (⟨fun y : N => (⟨y.val,hNW y.property⟩ : W),continuous_subtype_val.subtype_mk _⟩ : C(N,W))
      ((⟨fun x : A => (⟨x.val,hAW x.property⟩ : W),continuous_subtype_val.subtype_mk _⟩ : C(A,W)).comp
        (endpointRetraction d N hNA)) := by
  refine ⟨⟨fun t => ⟨d.homotopy (t.1,t.2.val),d.preserves t.1 t.2.val (hNW t.2.property)⟩,
    (d.homotopy.continuous.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩,?_,?_⟩
  · intro x
    exact Subtype.ext (d.zero x.val)
  · intro x
    rfl

end TernaryPoly.BoundaryNeighborhood
