module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LeviCrossedAction

@[expose] public section


/-!
# Classes of crossed cocycles, stated generically

These wrappers are stated for an arbitrary
representation, where the comparison is trivial, and are then used at `levelRep (n + 1) (-1)`:
`qcls ρ z` is the class of a crossed cocycle `z` in `CrossedH1 ρ`, and `quotLin ρ f` is `f`
followed by this quotient map.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot

variable {GroupType Value : Type} [Group GroupType] [AddCommGroup Value] [Module ℂ Value]
  (ρ : Representation ℂ GroupType Value)

/-- The class of a crossed cocycle in `CrossedH1 ρ`. -/
def qcls (z : crossedCocycles ρ) : CrossedH1 ρ := Submodule.Quotient.mk z

theorem qcls_eq_zero_iff (z : crossedCocycles ρ) : qcls ρ z = 0 ↔ z ∈ crossedBoundaries ρ :=
  Submodule.Quotient.mk_eq_zero _

theorem qcls_eq_qcls_iff (z z' : crossedCocycles ρ) :
    qcls ρ z = qcls ρ z' ↔ z - z' ∈ crossedBoundaries ρ :=
  Submodule.Quotient.eq _

theorem qcls_add (z z' : crossedCocycles ρ) : qcls ρ (z + z') = qcls ρ z + qcls ρ z' := rfl

theorem qcls_smul (a : ℂ) (z : crossedCocycles ρ) : qcls ρ (a • z) = a • qcls ρ z := rfl

/-- A linear map into the crossed cocycles, followed by the quotient map. -/
def quotLin {A : Type} [AddCommGroup A] [Module ℂ A] (f : A →ₗ[ℂ] crossedCocycles ρ) :
    A →ₗ[ℂ] CrossedH1 ρ :=
  (crossedBoundaries ρ).mkQ.comp f

theorem quotLin_apply {A : Type} [AddCommGroup A] [Module ℂ A] (f : A →ₗ[ℂ] crossedCocycles ρ)
    (a : A) : quotLin ρ f a = qcls ρ (f a) := rfl

theorem quotLin_eq {A : Type} [AddCommGroup A] [Module ℂ A] (f : A →ₗ[ℂ] crossedCocycles ρ)
    (a a' : A) (h : f a - f a' ∈ crossedBoundaries ρ) : quotLin ρ f a = quotLin ρ f a' := by
  rw [quotLin_apply, quotLin_apply, qcls_eq_qcls_iff]
  exact h

end TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot
