module

public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
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
# Morphisms out of permutation representations; projectivity of free permutation modules

For a `Γ`-set `H`, a morphism `ℚ[H] ⟶ A` of rational `Γ`-representations is the same as an equivariant
function `H → A` (`homFunEquiv`).  If `Γ` acts freely on `Y`, the permutation representation `ℚ[Y]` is
projective (`projective_ofMulAction`): an equivariant function lifts through a surjection by choosing
preimages on orbit representatives and translating.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.TopHomology

section HomFun

variable {Γ : Type} [Group Γ] (H : Type) [MulAction Γ H] (A : Rep.{0} ℚ Γ)

/-- The linear map out of `ℚ[H]` attached to a function `H → A`. -/
def liftMap (F : H → A) : MonoidAlgebra ℚ H →ₗ[ℚ] A :=
  Finsupp.linearCombination ℚ F ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

omit [MulAction Γ H] in
theorem liftMap_single (F : H → A) (h : H) (r : ℚ) :
    liftMap H A F (MonoidAlgebra.single h r) = r • F h := by
  simp [liftMap]

/-- The morphism `ℚ[H] ⟶ A` attached to an equivariant function. -/
def ofMulActionLift (F : H → A) (hF : ∀ γ h, F (γ • h) = A.ρ γ (F h)) :
    Rep.ofMulAction ℚ Γ H ⟶ A :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap (Representation.ofMulAction ℚ Γ H) A.ρ
    (liftMap H A F) (fun γ v => by
    have key : (liftMap H A F) ∘ₗ (Representation.ofMulAction ℚ Γ H γ) =
        (A.ρ γ) ∘ₗ (liftMap H A F) := by
      apply MonoidAlgebra.lhom_ext'
      intro x
      apply LinearMap.ext_ring
      simp [MonoidAlgebra.lsingle_apply, liftMap_single, hF]
    exact LinearMap.congr_fun key v))

theorem ofMulActionLift_single (F : H → A) (hF : ∀ γ h, F (γ • h) = A.ρ γ (F h)) (h : H) :
    (ofMulActionLift H A F hF).hom (MonoidAlgebra.single h 1) = F h := by
  simp [ofMulActionLift, liftMap_single]

theorem hom_ext_single {φ ψ : Rep.ofMulAction ℚ Γ H ⟶ A}
    (h : ∀ x : H, φ.hom (MonoidAlgebra.single x 1) = ψ.hom (MonoidAlgebra.single x 1)) : φ = ψ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  simpa [MonoidAlgebra.lsingle_apply] using h x

/-- Equivariant functions `H → A`. -/
def equivFun : Submodule ℚ (H → A) where
  carrier := {F | ∀ γ h, F (γ • h) = A.ρ γ (F h)}
  zero_mem' := fun γ h => by simp
  add_mem' := fun {F G} hF hG γ h => by simp [hF γ h, hG γ h]
  smul_mem' := fun c F hF γ h => by simp [hF γ h]

/-- Morphisms out of the permutation representation are equivariant functions. -/
def homFunEquiv : (Rep.ofMulAction ℚ Γ H ⟶ A) ≃ₗ[ℚ] equivFun H A where
  toFun φ := ⟨fun h => φ.hom (MonoidAlgebra.single h 1), fun γ h => by
    have := Rep.hom_comm_apply φ γ (MonoidAlgebra.single h 1)
    simpa [Representation.ofMulAction_single] using this⟩
  invFun F := ofMulActionLift H A F.1 F.2
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
  left_inv φ := hom_ext_single H A (fun x => ofMulActionLift_single H A _ _ x)
  right_inv F := by
    apply Subtype.ext
    funext h
    exact ofMulActionLift_single H A F.1 F.2 h

theorem homFunEquiv_apply (φ : Rep.ofMulAction ℚ Γ H ⟶ A) (h : H) :
    (homFunEquiv H A φ).1 h = φ.hom (MonoidAlgebra.single h 1) := rfl

end HomFun

section Projective

variable {Γ : Type} [Group Γ] (Y : Type) [MulAction Γ Y]

/-- The permutation representation of a free `Γ`-set is projective. -/
theorem projective_ofMulAction (hfree : ∀ (γ : Γ) (y : Y), γ • y = y → γ = 1) :
    Projective (Rep.ofMulAction ℚ Γ Y) := by
  classical
  refine ⟨fun {E X} f e he => ?_⟩
  have hsurj : Function.Surjective e.hom := (Rep.epi_iff_surjective e).mp he
  let s : Y → Y := fun y => Quotient.out (Quotient.mk (MulAction.orbitRel Γ Y) y)
  have hs : ∀ y, ∃ γ : Γ, γ • s y = y := fun y => by
    have h : (MulAction.orbitRel Γ Y) y (s y) :=
      (MulAction.orbitRel Γ Y).symm (Quotient.mk_out (s := MulAction.orbitRel Γ Y) y)
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp h
    exact ⟨γ, hγ⟩
  let g : Y → Γ := fun y => Classical.choose (hs y)
  have hg : ∀ y, g y • s y = y := fun y => Classical.choose_spec (hs y)
  have hs_eq : ∀ (γ : Γ) (y : Y), s (γ • y) = s y := fun γ y => by
    have : Quotient.mk (MulAction.orbitRel Γ Y) (γ • y) = Quotient.mk (MulAction.orbitRel Γ Y) y :=
      Quotient.sound (MulAction.orbitRel_apply.mpr ⟨γ, rfl⟩)
    simp only [s, this]
  have hg_eq : ∀ (γ : Γ) (y : Y), g (γ • y) = γ * g y := fun γ y => by
    have h1 : g (γ • y) • s y = γ • y := by
      have := hg (γ • y)
      rwa [hs_eq] at this
    have h2 : (γ * g y) • s y = γ • y := by rw [mul_smul, hg]
    have h3 : ((γ * g y)⁻¹ * g (γ • y)) • s y = s y := by
      rw [mul_smul, h1, ← h2, inv_smul_smul]
    have := hfree _ _ h3
    calc g (γ • y) = (γ * g y) * ((γ * g y)⁻¹ * g (γ • y)) := (mul_inv_cancel_left _ _).symm
      _ = γ * g y := by rw [this, mul_one]
  let F : Y → X := fun y => f.hom (MonoidAlgebra.single y 1)
  have hF : ∀ γ y, F (γ • y) = X.ρ γ (F y) := fun γ y => by
    have := Rep.hom_comm_apply f γ (MonoidAlgebra.single y 1)
    simpa [F, Representation.ofMulAction_single] using this
  let a' : Y → E := fun y => Classical.choose (hsurj (F y))
  have ha' : ∀ y, e.hom (a' y) = F y := fun y => Classical.choose_spec (hsurj (F y))
  let F' : Y → E := fun y => E.ρ (g y) (a' (s y))
  have hF' : ∀ γ y, F' (γ • y) = E.ρ γ (F' y) := fun γ y => by
    simp only [F', hg_eq, hs_eq, map_mul, Module.End.mul_apply]
  refine ⟨ofMulActionLift Y E F' hF', hom_ext_single Y X (fun y => ?_)⟩
  change e.hom ((ofMulActionLift Y E F' hF').hom (MonoidAlgebra.single y 1)) = F y
  rw [ofMulActionLift_single]
  simp only [F']
  rw [Rep.hom_comm_apply, ha', ← hF, hg]

end Projective

end TernaryPeriodPolynomials.Argument.TopHomology
