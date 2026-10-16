module

public import TernaryPeriodPolynomials.Topology.InwardHomotopyBasic
public import Mathlib.Topology.Compactness.Compact

@[expose] public section


noncomputable section
namespace TernaryPoly.InwardHomotopy
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X] {U : Set X}

/-- The stationary deformation supplies the empty finite composition. -/
def LocalDeformation.identity (U : Set X) : LocalDeformation U where
  homotopy := ContinuousMap.snd
  zero _ := rfl
  preserves _ _ hx := hx
  endpoint_fixed _ _ := rfl

/-- Compose two local deformations at the same time parameter. -/
def LocalDeformation.comp (a b : LocalDeformation U) : LocalDeformation U where
  homotopy := ⟨fun p => a.homotopy (p.1,b.homotopy p),
    a.homotopy.continuous.comp (continuous_fst.prodMk b.homotopy.continuous)⟩
  zero x := by simp only [ContinuousMap.coe_mk,b.zero,a.zero]
  preserves t x hx := a.preserves t _ (b.preserves t x hx)
  endpoint_fixed x hx := by
    have hb : b.homotopy (1,x)∉U := fun h => hx (a.preserves 1 _ h)
    exact (a.endpoint_fixed _ hx).trans (b.endpoint_fixed x hb)

/-- Once a point reaches the interior it remains there under every subsequent deformation. -/
theorem LocalDeformation.comp_pushes_right (a b : LocalDeformation U) (x : X)
    (hx : b.homotopy (1,x)∈U) : (a.comp b).homotopy (1,x)∈U :=
  a.preserves 1 _ hx

/-- If the second deformation did not push a boundary point, it fixed that point, so the first
one still pushes it. No displacement estimate is needed. -/
theorem LocalDeformation.comp_pushes_left (a b : LocalDeformation U) (x : X)
    (hx : a.homotopy (1,x)∈U) : (a.comp b).homotopy (1,x)∈U := by
  by_cases hb : b.homotopy (1,x)∈U
  · exact a.comp_pushes_right b x hb
  · change a.homotopy (1,b.homotopy (1,x))∈U
    rw [b.endpoint_fixed x hb]
    exact hx

/-- Finite simultaneous composition of genuine continuous local deformations. -/
def combine : List (LocalDeformation U) → LocalDeformation U
  | [] => .identity U
  | a::l => a.comp (combine l)

theorem combine_pushes {l : List (LocalDeformation U)} {a : LocalDeformation U}
    (ha : a∈l) (x : X) (hx : a.homotopy (1,x)∈U) : (combine l).homotopy (1,x)∈U := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst a
      exact b.comp_pushes_left (combine l) x hx
    · exact b.comp_pushes_right (combine l) x (ih h)

/-- Compactness turns pointwise inward deformations into one global interior-preserving
homotopy with its full endpoint image in the interior. -/
theorem exists_global [CompactSpace X] (hU : IsOpen U)
    (hlocal : ∀ x : X, ∃ d : LocalDeformation U, d.homotopy (1,x)∈U) :
    ∃ d : LocalDeformation U, ∀ x, d.homotopy (1,x)∈U := by
  classical
  let d : X → LocalDeformation U := fun x => (hlocal x).choose
  let V : X → Set X := fun x => {y | (d x).homotopy (1,y)∈U}
  have hV : ∀ x, IsOpen (V x) := fun x =>
    hU.preimage ((d x).homotopy.continuous.comp (continuous_const.prodMk continuous_id))
  have hcover : (Set.univ : Set X) ⊆ ⋃ y, V y := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,(hlocal x).choose_spec⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover V hV hcover
  refine ⟨combine (s.toList.map d),fun x => ?_⟩
  obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact combine_pushes (List.mem_map.mpr ⟨y,Finset.mem_toList.mpr hy,rfl⟩) x hxy

/-- A global inward homotopy gives a homotopy equivalence whose forward map is the literal
inclusion of the designated interior. -/
def homotopyEquivOfGlobal (d : LocalDeformation U) (hend : ∀ x, d.homotopy (1,x)∈U) :
    ContinuousMap.HomotopyEquiv U X where
  toFun := ⟨Subtype.val,continuous_subtype_val⟩
  invFun := ⟨fun x => ⟨d.homotopy (1,x),hend x⟩,
    (d.homotopy.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  left_inv := by
    apply Nonempty.intro
    apply ContinuousMap.Homotopy.symm
    refine ⟨⟨fun p => ⟨d.homotopy (p.1,p.2.val),d.preserves _ _ p.2.property⟩,
      (d.homotopy.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩,?_,?_⟩
    · intro x
      apply Subtype.ext
      exact d.zero x.val
    · intro x
      rfl
  right_inv := by
    apply Nonempty.intro
    apply ContinuousMap.Homotopy.symm
    exact ⟨d.homotopy,d.zero,fun _ => rfl⟩

@[simp] theorem homotopyEquivOfGlobal_apply (d : LocalDeformation U)
    (hend : ∀ x, d.homotopy (1,x)∈U) (x : U) : homotopyEquivOfGlobal d hend x=x.val := rfl

/-- The exact inclusion is a homotopy equivalence under the proved finite local criterion. -/
theorem exists_homotopyEquiv [CompactSpace X] (hU : IsOpen U)
    (hlocal : ∀ x : X, ∃ d : LocalDeformation U, d.homotopy (1,x)∈U) :
    ∃ e : ContinuousMap.HomotopyEquiv U X, ∀ x, e x=x.val := by
  obtain ⟨d,hd⟩ := exists_global hU hlocal
  exact ⟨homotopyEquivOfGlobal d hd,fun _ => rfl⟩

end TernaryPoly.InwardHomotopy
