module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.Finite
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
namespace TernaryPoly.CochainExcisionAlgebra
open CategoryTheory Limits HomologicalComplex

/-- A signed exact cochain square identifies the two actual restriction kernels. -/
theorem kernel_map_isIso_of_shortExact {C : Type*} [Category C] [Abelian C]
    {S U V I : C} (u : S ⟶ U) (v : S ⟶ V) (a : U ⟶ I) (b : V ⟶ I)
    (h : v ≫ b = u ≫ a)
    (he : (ShortComplex.mk (biprod.lift u v) (biprod.desc a (-b))
      (by simp [biprod.lift_desc,Preadditive.comp_neg,h])).ShortExact) :
    IsIso (kernel.map u b v a h.symm) := by
  let Q := ShortComplex.mk (biprod.lift u v) (biprod.desc a (-b))
    (by simp [biprod.lift_desc,Preadditive.comp_neg,h])
  have hQ : Q.ShortExact := he
  have : Mono Q.f := hQ.mono_f
  let t : kernel b ⟶ S := hQ.exact.lift (biprod.lift 0 (kernel.ι b))
    (by simp [Q,biprod.lift_desc,Preadditive.comp_neg])
  have ht : t ≫ biprod.lift u v = biprod.lift 0 (kernel.ι b) := hQ.exact.lift_f _ _
  have hu : t ≫ u = 0 := by
    have h' := congrArg (fun f => f ≫ biprod.fst) ht
    simpa using h'
  have hv : t ≫ v = kernel.ι b := by
    have h' := congrArg (fun f => f ≫ biprod.snd) ht
    simpa using h'
  let s : kernel b ⟶ kernel u := kernel.lift u t hu
  refine ⟨s, ?_, ?_⟩
  · apply (cancel_mono (kernel.ι u)).mp
    simp only [kernel.map,Category.assoc,s,kernel.lift_ι,Category.id_comp]
    apply (cancel_mono Q.f).mp
    change _ ≫ biprod.lift u v = kernel.ι u ≫ biprod.lift u v
    apply biprod.hom_ext
    · simp only [Category.assoc,biprod.lift_fst]
      rw [hu,comp_zero,kernel.condition]
    · simp only [Category.assoc,biprod.lift_snd]
      rw [hv]
      simp
  · apply (cancel_mono (kernel.ι b)).mp
    simp only [kernel.map,Category.assoc,kernel.lift_ι,Category.id_comp]
    rw [← Category.assoc,show s ≫ kernel.ι u = t from kernel.lift_ι _ _ _,hv]

end TernaryPoly.CochainExcisionAlgebra
