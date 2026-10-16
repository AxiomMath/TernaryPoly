module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Basic
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
namespace TernaryPoly.SmoothSingularGlobal
open Set Function

def familySupport {ι : Type*} {A : ι → Type*} [∀ i, Zero (A i)] (w : ∀ i, A i) : Set ι :=
  {i | w i ≠ 0}

variable {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)] [∀ i, Module ℝ (A i)]

/-- Families with only finitely many nonzero components, as a literal submodule of the product. -/
def finiteFamilySubmodule : Submodule ℝ (∀ i, A i) where
  carrier := {w | (familySupport w).Finite}
  zero_mem' := by simp [familySupport]
  add_mem' := by
    intro w z hw hz
    apply (hw.union hz).subset
    intro i hi
    by_contra h
    have hwz : w i = 0 ∧ z i = 0 := by simpa only [mem_union, familySupport, mem_ofPred_eq, not_or, not_not] using h
    exact hi (by simp [hwz.1,hwz.2])
  smul_mem' := by
    intro c w hw
    apply hw.subset
    intro i hi
    change w i ≠ 0
    contrapose! hi
    simp only [familySupport, mem_ofPred_eq, not_not, Pi.smul_apply]
    rw [hi,smul_zero]

/-- Componentwise real linear maps preserve finite nonzero support. -/
theorem finiteFamily_map {B : ι → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Module ℝ (B i)]
    (f : ∀ i, A i →ₗ[ℝ] B i) {w : ∀ i, A i} (hw : (familySupport w).Finite) :
    (familySupport (fun i => f i (w i))).Finite := by
  apply hw.subset
  intro i hi
  change w i ≠ 0
  contrapose! hi
  simp only [familySupport, mem_ofPred_eq, not_not]
  rw [hi,map_zero]

/-- Componentwise primitive choices which preserve zero preserve finite support. -/
theorem finiteFamily_primitive {B : ι → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Module ℝ (B i)]
    (f : ∀ i, B i →ₗ[ℝ] A i) (w : ∀ i, A i) (hw : (familySupport w).Finite)
    (he : ∀ i, ∃ z, f i z = w i ∧ (w i = 0 → z = 0)) :
    ∃ z : ∀ i, B i, (familySupport z).Finite ∧ ∀ i, f i (z i) = w i := by
  choose z hz hz0 using he
  refine ⟨z,hw.subset ?_,hz⟩
  intro i hi
  change w i ≠ 0
  contrapose! hi
  simpa only [familySupport, mem_ofPred_eq, not_not] using hz0 i hi

end TernaryPoly.SmoothSingularGlobal
