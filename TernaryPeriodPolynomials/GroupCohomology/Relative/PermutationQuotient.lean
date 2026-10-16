module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Control.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section

noncomputable section
namespace TernaryPoly.RelativePermutationQuotient
variable {A B : Type*}
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Finite chains on the complement of a specified subset of indices. -/
abbrev Outside (p : B → Prop) := {b : B // ¬p b}

/-- Delete exactly the inside coordinates, retaining the literal outside indices. -/
def project (p : B → Prop) : (B →₀ ℚ) →ₗ[ℚ] (Outside p →₀ ℚ) :=
  Finsupp.lsum ℚ (fun b => if h : p b then 0 else Finsupp.lsingle ⟨b,h⟩)

@[simp] theorem project_single (p : B → Prop) (b : B) (q : ℚ) :
    project p (Finsupp.single b q) = if h : p b then 0 else Finsupp.single ⟨b,h⟩ q := by
  by_cases h : p b <;> simp [project,h,Finsupp.lsum_single]

/-- Literal re-inclusion of the outside coordinates. -/
def includeOutside (p : B → Prop) : (Outside p →₀ ℚ) →ₗ[ℚ] (B →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ Subtype.val

@[simp] theorem includeOutside_single (p : B → Prop) (b : Outside p) (q : ℚ) :
    includeOutside p (Finsupp.single b q) = Finsupp.single b.val q := Finsupp.mapDomain_single

theorem project_includeOutside (p : B → Prop) (c : Outside p →₀ ℚ) :
    project p (includeOutside p c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single b q => simp only [includeOutside_single,project_single,dite_eq_right b.property]

variable (f : A → B) (p : B → Prop) (hf : ∀ b, (∃ a, f a = b) ↔ p b)

/-- The exact image of the finite-chain inclusion. -/
def insideImage : Submodule ℚ (B →₀ ℚ) := (Finsupp.lmapDomain ℚ ℚ f).range

/-- A chosen inside preimage, used only to prove exactness of the literal coordinate projection. -/
def insideLift : (B →₀ ℚ) →ₗ[ℚ] (A →₀ ℚ) :=
  Finsupp.lsum ℚ (fun b => if h : p b then Finsupp.lsingle ((hf b).mpr h).choose else 0)

theorem decomposition (c : B →₀ ℚ) :
    Finsupp.lmapDomain ℚ ℚ f (insideLift f p hf c) + includeOutside p (project p c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero,add_zero]
  | add c d hc hd => simp only [map_add]; rw [add_add_add_comm,hc,hd]
  | single b q =>
    by_cases h : p b
    · simp only [insideLift,Finsupp.lsum_single,Finsupp.lsingle_apply,
        Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,project_single,dite_eq_left h,map_zero,add_zero]
      rw [((hf b).mpr h).choose_spec]
    · simp only [insideLift,Finsupp.lsum_single,LinearMap.zero_apply,map_zero,
        project_single,dite_eq_right h,includeOutside_single,zero_add]

include hf in
theorem project_inclusion (c : A →₀ ℚ) : project p (Finsupp.lmapDomain ℚ ℚ f c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd,add_zero]
  | single a q =>
    simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,project_single,
      dite_eq_left ((hf (f a)).mp ⟨a,rfl⟩)]

include hf in
theorem ker_project : (project p).ker = insideImage f := by
  apply le_antisymm
  · intro c hc
    refine ⟨insideLift f p hf c,?_⟩
    have hd := decomposition f p hf c
    rw [LinearMap.mem_ker.mp hc,map_zero,add_zero] at hd
    exact hd
  · rintro _ ⟨c,rfl⟩
    exact project_inclusion f p hf c

/-- The finite-chain quotient is explicitly the finite-chain module on the complementary indices. -/
def quotientEquiv : ((B →₀ ℚ) ⧸ insideImage f) ≃ₗ[ℚ] (Outside p →₀ ℚ) where
  toLinearMap := (insideImage f).liftQ (project p) (by rw [ker_project f p hf])
  invFun c := (insideImage f).mkQ (includeOutside p c)
  left_inv x := by
    refine Submodule.Quotient.induction_on (insideImage f) x ?_
    intro c
    change (insideImage f).mkQ (includeOutside p (project p c)) = (insideImage f).mkQ c
    have hd := congrArg (insideImage f).mkQ (decomposition f p hf c)
    rw [map_add,show (insideImage f).mkQ (Finsupp.lmapDomain ℚ ℚ f (insideLift f p hf c)) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨insideLift f p hf c,rfl⟩,zero_add] at hd
    exact hd
  right_inv c := project_includeOutside p c

@[simp] theorem quotientEquiv_mk (c : B →₀ ℚ) :
    quotientEquiv f p hf (Submodule.Quotient.mk c) = project p c := rfl

/-- Specialization to the inclusion of a subtype, with no geometric assumptions. -/
def subtypeQuotientEquiv (p : B → Prop) :
    ((B →₀ ℚ) ⧸ insideImage (Subtype.val : Subtype p → B)) ≃ₗ[ℚ] (Outside p →₀ ℚ) :=
  quotientEquiv Subtype.val p (fun b => ⟨fun ⟨a,ha⟩ => ha ▸ a.property,fun h => ⟨⟨b,h⟩,rfl⟩⟩)

/-- A subset-preserving permutation restricts to the actual complementary indices. -/
def outsideEquiv (e : B ≃ B) (he : ∀ b, p (e b) ↔ p b) : Outside p ≃ Outside p :=
  e.subtypeEquiv (fun b => (not_congr (he b)).symm)

/-- Complement projection is natural for every actual subset-preserving permutation. -/
theorem project_natural (e : B ≃ B) (he : ∀ b, p (e b) ↔ p b) (c : B →₀ ℚ) :
    project p (Finsupp.domLCongr (R := ℚ) e c) = Finsupp.domLCongr (R := ℚ) (outsideEquiv p e he) (project p c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single b q =>
    by_cases h : p b
    · simp only [Finsupp.domLCongr_single,project_single,dite_eq_left h,dite_eq_left ((he b).mpr h),map_zero]
    · simp only [Finsupp.domLCongr_single,project_single,dite_eq_right h,
        dite_eq_right (fun hp => h ((he b).mp hp)),Finsupp.domLCongr_single]
      rfl

section SumCoordinates
variable {X Y Z : Type*}

@[simp] theorem split_single_inl (x : X) (q : ℚ) :
    Finsupp.sumFinsuppLEquivProdFinsupp ℚ (Finsupp.single (.inl x : X ⊕ Y) q) =
      (Finsupp.single x q,0) := by
  apply Prod.ext <;> ext y <;> simp

@[simp] theorem split_single_inr (y : Y) (q : ℚ) :
    Finsupp.sumFinsuppLEquivProdFinsupp ℚ (Finsupp.single (.inr y : X ⊕ Y) q) =
      (0,Finsupp.single y q) := by
  apply Prod.ext <;> ext x <;> simp

/-- Reindexing finite chains respects an actual commuting square of index permutations. -/
theorem reindex_natural (e : X ≃ Y) (g : X ≃ X) (h : Y ≃ Y)
    (he : ∀ x, e (g x) = h (e x)) (c : X →₀ ℚ) :
    Finsupp.domLCongr (R := ℚ) e (Finsupp.domLCongr (R := ℚ) g c) =
      Finsupp.domLCongr (R := ℚ) h (Finsupp.domLCongr (R := ℚ) e c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single x q => simp only [Finsupp.domLCongr_single,he]

/-- The two finite direct-sum coordinates carry the independent literal permutation actions. -/
theorem split_natural (e : X ≃ X) (f : Y ≃ Y) (c : X ⊕ Y →₀ ℚ) :
    Finsupp.sumFinsuppLEquivProdFinsupp ℚ
      (Finsupp.domLCongr (R := ℚ) (Equiv.sumCongr e f) c) =
    ((Finsupp.domLCongr (R := ℚ) e).prodCongr (Finsupp.domLCongr (R := ℚ) f))
      (Finsupp.sumFinsuppLEquivProdFinsupp ℚ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single x q =>
    cases x <;> simp only [Finsupp.domLCongr_single,Equiv.sumCongr_apply,
      Sum.map_inl,Sum.map_inr,split_single_inl,split_single_inr,LinearEquiv.prodCongr_apply,map_zero]

end SumCoordinates
end TernaryPoly.RelativePermutationQuotient
