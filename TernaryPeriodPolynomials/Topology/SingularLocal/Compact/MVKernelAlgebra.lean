module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.Control.Basic
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Set.Piecewise
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Util.Qq

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits

variable {C : Type*} [Category C] [Abelian C] {X A D : C} (r : X ⟶ A) (s : X ⟶ D)

/-- The actual left inclusion from the joint restriction kernel. -/
def kernelPairLeft : kernel (biprod.lift r s) ⟶ kernel r :=
  kernel.lift r (kernel.ι (biprod.lift r s)) (by
    have h := congrArg (fun f => f ≫ biprod.fst) (kernel.condition (biprod.lift r s))
    simpa only [Category.assoc,biprod.lift_fst,zero_comp] using h)

/-- The actual right inclusion from the joint restriction kernel. -/
def kernelPairRight : kernel (biprod.lift r s) ⟶ kernel s :=
  kernel.lift s (kernel.ι (biprod.lift r s)) (by
    have h := congrArg (fun f => f ≫ biprod.snd) (kernel.condition (biprod.lift r s))
    simpa only [Category.assoc,biprod.lift_snd,zero_comp] using h)

/-- The joint restriction kernel enters the kernel of the sum by the signed pair. -/
def kernelPairToSum : kernel (biprod.lift r s) ⟶ kernel (biprod.desc (kernel.ι r) (kernel.ι s)) :=
  kernel.lift _ (biprod.lift (kernelPairLeft r s) (-kernelPairRight r s)) (by
    simp [biprod.lift_desc,kernelPairLeft,kernelPairRight,Preadditive.neg_comp])

/-- The two ambient components of a sum-kernel element add to zero. -/
theorem kernelSum_components :
    (kernel.ι (biprod.desc (kernel.ι r) (kernel.ι s)) ≫ biprod.fst) ≫ kernel.ι r +
      (kernel.ι (biprod.desc (kernel.ι r) (kernel.ι s)) ≫ biprod.snd) ≫ kernel.ι s = 0 := by
  have h := kernel.condition (biprod.desc (kernel.ι r) (kernel.ι s))
  simpa only [biprod.desc_eq,Preadditive.comp_add,Category.assoc] using h

/-- Recover the joint restriction kernel from the actual first ambient component of a sum-kernel element. -/
def kernelSumToPair : kernel (biprod.desc (kernel.ι r) (kernel.ι s)) ⟶ kernel (biprod.lift r s) :=
  kernel.lift _ ((kernel.ι (biprod.desc (kernel.ι r) (kernel.ι s)) ≫ biprod.fst) ≫ kernel.ι r) (by
    apply biprod.hom_ext
    · simp
    · have h := congrArg (fun f => f ≫ s) (kernelSum_components r s)
      simpa only [Preadditive.add_comp,Category.assoc,kernel.condition,comp_zero,zero_comp,add_zero,
        biprod.lift_snd] using h)

/-- The actual signed pair identifies the joint restriction kernel with the kernel of the sum. -/
def kernelPairSumIso : kernel (biprod.lift r s) ≅ kernel (biprod.desc (kernel.ι r) (kernel.ι s)) where
  hom := kernelPairToSum r s
  inv := kernelSumToPair r s
  hom_inv_id := by
    apply (cancel_mono (kernel.ι (biprod.lift r s))).mp
    simp [kernelPairToSum,kernelSumToPair,kernelPairLeft,Category.assoc]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι (biprod.desc (kernel.ι r) (kernel.ι s)))).mp
    apply biprod.hom_ext
    · apply (cancel_mono (kernel.ι r)).mp
      simp [kernelPairToSum,kernelSumToPair,kernelPairLeft,Category.assoc]
    · apply (cancel_mono (kernel.ι s)).mp
      simp only [kernelPairToSum,kernelSumToPair,Category.assoc,kernel.lift_ι,biprod.lift_snd,
        kernelPairRight,Preadditive.comp_neg,Preadditive.neg_comp,Category.id_comp]
      have h := kernelSum_components r s
      rw [Category.assoc,Category.assoc] at h
      exact neg_eq_iff_add_eq_zero.mpr h

end TernaryPoly.SingularLocalCompactMV
