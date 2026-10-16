module

public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.Perm.Option
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
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Coinvariants of `trivial ⊗ X`

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HomologyBridge

open CategoryTheory Representation

variable {G : Type} [Group G] (Λ : Subgroup G) (A : Rep ℂ G)

section Tensor

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The `Λ`-coinvariants of `X` map to those of `ℂ ⊗ X` (trivial first factor). -/
def toTensor : Coinvariants (ρ.comp Λ.subtype) →ₗ[ℂ]
    Coinvariants (((Representation.trivial ℂ G ℂ).tprod ρ).comp Λ.subtype) :=
  Coinvariants.lift _ ((Coinvariants.mk _).comp (TensorProduct.mk ℂ ℂ V 1)) fun γ => by
    ext v
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply]
    have := Coinvariants.mk_self_apply (ρ := ((Representation.trivial ℂ G ℂ).tprod ρ).comp Λ.subtype) γ
      ((1 : ℂ) ⊗ₜ[ℂ] v)
    simpa using this

/-- The inverse: `a ⊗ x ↦ a • [x]`. -/
def fromTensor : Coinvariants (((Representation.trivial ℂ G ℂ).tprod ρ).comp Λ.subtype) →ₗ[ℂ]
    Coinvariants (ρ.comp Λ.subtype) :=
  Coinvariants.lift _
    (TensorProduct.lift ((LinearMap.lsmul ℂ (Coinvariants (ρ.comp Λ.subtype))).flip.comp
      (Coinvariants.mk (ρ.comp Λ.subtype))).flip) fun γ => by
    apply TensorProduct.ext'
    intro a v
    have h := Coinvariants.mk_self_apply (ρ.comp Λ.subtype) γ v
    simp
    exact congrArg (fun z => a • z) h

theorem fromTensor_toTensor (x : Coinvariants (ρ.comp Λ.subtype)) :
    fromTensor Λ ρ (toTensor Λ ρ x) = x := by
  induction x using Coinvariants.induction_on with
  | h v => simp [toTensor, fromTensor]

theorem toTensor_fromTensor
    (x : Coinvariants (((Representation.trivial ℂ G ℂ).tprod ρ).comp Λ.subtype)) :
    toTensor Λ ρ (fromTensor Λ ρ x) = x := by
  induction x using Coinvariants.induction_on with
  | h v =>
    induction v using TensorProduct.inductionOn with
    | tmul a w =>
      simp [toTensor, fromTensor]
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add u w hu hw => simp [map_add, hu, hw]

end Tensor

end TernaryPeriodPolynomials.Argument.HomologyBridge
