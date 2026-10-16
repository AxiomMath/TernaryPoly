module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UnitInterval
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
namespace TernaryPoly.SymmetricSpaceBoundaryMV.OpenGlue
open Topology
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X]
variable (V N : Set X) (hV : IsOpen V) (hN : IsOpen N)
variable (H : C(I × N,X)) (hfix : ∀ (t : I) (x : N), x.val∈V → H (t,x)=x.val)

abbrev UnionSpace := V ∪ N

def domains : Bool → Set (I × UnionSpace V N)
  | false => {z | z.2.val∈V}
  | true => {z | z.2.val∈N}

def pieces : (b : Bool) → C(domains V N b,X)
  | false => ⟨fun z => z.val.2.val,
      continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)⟩
  | true => ⟨fun z => H (z.val.1,⟨z.val.2.val,z.property⟩),
      H.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _))⟩

include hfix in
theorem pieces_agree (i j : Bool) (z : I × UnionSpace V N)
    (hi : z∈domains V N i) (hj : z∈domains V N j) :
    pieces V N H i ⟨z,hi⟩ = pieces V N H j ⟨z,hj⟩ := by
  cases i <;> cases j
  · rfl
  · exact (hfix z.1 ⟨z.2.val,hj⟩ hi).symm
  · exact hfix z.1 ⟨z.2.val,hi⟩ hj
  · rfl

include hV hN in
theorem domains_cover (z : I × UnionSpace V N) : ∃ b, domains V N b∈𝓝 z := by
  rcases z.2.property with h | h
  · exact ⟨false,(hV.preimage (continuous_subtype_val.comp continuous_snd)).mem_nhds h⟩
  · exact ⟨true,(hN.preimage (continuous_subtype_val.comp continuous_snd)).mem_nhds h⟩

def homotopy : C(I × UnionSpace V N,X) :=
  ContinuousMap.liftCover (domains V N) (pieces V N H) (pieces_agree V N H hfix)
    (domains_cover V N hV hN)

theorem homotopy_of_mem_left (t : I) (x : UnionSpace V N) (hx : x.val∈V) :
    homotopy V N hV hN H hfix (t,x)=x.val :=
  ContinuousMap.liftCover_coe (i := false) ⟨(t,x),hx⟩

theorem homotopy_of_mem_right (t : I) (x : UnionSpace V N) (hx : x.val∈N) :
    homotopy V N hV hN H hfix (t,x)=H (t,⟨x.val,hx⟩) :=
  ContinuousMap.liftCover_coe (i := true) ⟨(t,x),hx⟩

theorem homotopy_zero (hzero : ∀ x : N,H (0,x)=x.val) (x : UnionSpace V N) :
    homotopy V N hV hN H hfix (0,x)=x.val := by
  rcases x.property with hx | hx
  · exact homotopy_of_mem_left V N hV hN H hfix 0 x hx
  · rw [homotopy_of_mem_right V N hV hN H hfix 0 x hx,hzero]

theorem homotopy_preserves (hpres : ∀ (t : I) (x : N),H (t,x)∈N)
    (t : I) (x : UnionSpace V N) : homotopy V N hV hN H hfix (t,x)∈V ∪ N := by
  rcases x.property with hx | hx
  · rw [homotopy_of_mem_left V N hV hN H hfix t x hx]
    exact Or.inl hx
  · rw [homotopy_of_mem_right V N hV hN H hfix t x hx]
    exact Or.inr (hpres t ⟨x.val,hx⟩)

theorem homotopy_endpoint {A : Set X} (hVA : V⊆A) (hend : ∀ x : N,H (1,x)∈A)
    (x : UnionSpace V N) : homotopy V N hV hN H hfix (1,x)∈A := by
  rcases x.property with hx | hx
  · rw [homotopy_of_mem_left V N hV hN H hfix 1 x hx]
    exact hVA hx
  · rw [homotopy_of_mem_right V N hV hN H hfix 1 x hx]
    exact hend ⟨x.val,hx⟩

theorem homotopy_fixed {A : Set X}
    (hA : ∀ (t : I) (x : N),x.val∈A → H (t,x)=x.val)
    (t : I) (x : UnionSpace V N) (hx : x.val∈A) :
    homotopy V N hV hN H hfix (t,x)=x.val := by
  rcases x.property with h | h
  · exact homotopy_of_mem_left V N hV hN H hfix t x h
  · rw [homotopy_of_mem_right V N hV hN H hfix t x h]
    exact hA t ⟨x.val,h⟩ hx

end TernaryPoly.SymmetricSpaceBoundaryMV.OpenGlue
