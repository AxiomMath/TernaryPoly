module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.LevelSix
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Flags
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Cochains
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Isotropy

@[expose] public section


/-!
# The model cochains of `Γ(6)` as invariant functions on `V^{k+1} × Z`

`Γ(6)` (`principalSix`) embeds in `GL₃(ℚ)` (`iotaQ`, image `N6`) and acts freely on the ambient vertex set
`V = GL₃(ℚ)` by left multiplication (`vertexAction`, `vertexAction_free`).  For a `GL₃(ℚ)`-set `X`
equivariantly in bijection with a `Γ(6)`-set `Z` (`ψ : X ≃ Z`, `hψ`), the homogeneous scalar cochains
`cochains N6 (functionRepresentation scalarTrivial X) k` of the model are the same as the
`Γ(6)`-invariant complex functions on `V^{k+1} × Z` (`modelInvEquiv`, `F(x, z) = f(x)(ψ⁻¹ z)`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPoly.IntegralGL3Congruence (principalSix)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

/-- The abstract group `Γ(6)`. -/
abbrev Γ6 : Type := ↥principalSix

/-- The embedding of `Γ(6)` into `GL₃(ℚ)`. -/
def iotaQ : Γ6 →* RationalGL3 :=
  (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)).comp principalSix.subtype

theorem iotaQ_mem (γ : Γ6) : iotaQ γ ∈ N6 := ⟨γ.val, γ.2, rfl⟩

theorem exists_iotaQ_eq {n : RationalGL3} (h : n ∈ N6) : ∃ γ : Γ6, iotaQ γ = n := by
  obtain ⟨d, hd, rfl⟩ := h
  exact ⟨⟨d, hd⟩, rfl⟩

theorem iotaQ_injective : Function.Injective iotaQ := by
  intro a b h
  exact Subtype.ext (intMap_injective h)

/-- The action of `Γ(6)` on the ambient vertex set `GL₃(ℚ)` by left multiplication. -/
@[instance_reducible]
def vertexAction : MulAction Γ6 RationalGL3 := MulAction.compHom RationalGL3 iotaQ

/-- The vertex action is free. -/
theorem vertexAction_free : ∀ (γ : Γ6) (v : RationalGL3),
    (iotaQ γ * v = v) → γ = 1 := by
  intro γ v h
  have : iotaQ γ = 1 := by simpa using h
  exact iotaQ_injective (by simpa using this)

section Inv

variable (V Z : Type) [MulAction Γ6 V] [MulAction Γ6 Z]

/-- `Γ(6)`-invariant functions on `V^{k+1} × Z`. -/
def InvF (k : ℕ) : Submodule ℂ (((Fin (k + 1) → V) × Z) → ℂ) where
  carrier := {F | ∀ (γ : Γ6) y, F (γ • y) = F y}
  zero_mem' := fun γ y => rfl
  add_mem' := fun {F G} hF hG γ y => by simp [hF γ y, hG γ y]
  smul_mem' := fun c F hF γ y => by simp [hF γ y]

end Inv

attribute [local instance] vertexAction

section Model

variable {X Z : Type} [MulAction RationalGL3 X] [MulAction Γ6 Z] (ψ : X ≃ Z)
  (hψ : ∀ (γ : Γ6) (x : X), ψ (iotaQ γ • x) = γ • ψ x)

include hψ in
theorem symm_smul (γ : Γ6) (z : Z) : ψ.symm (γ • z) = iotaQ γ • ψ.symm z := by
  apply ψ.injective
  rw [Equiv.apply_symm_apply, hψ, Equiv.apply_symm_apply]

/-- Model cochains of `N6` for the flag set `X` as `Γ(6)`-invariant functions on `V^{k+1} × Z`. -/
def modelToInv (k : ℕ) :
    cochains N6 (functionRepresentation scalarTrivial X) k →ₗ[ℂ] InvF RationalGL3 Z k where
  toFun f := ⟨fun y => f.1 y.1 (ψ.symm y.2), by
    intro γ y
    have h1 := congrFun (f.2 ⟨iotaQ γ, iotaQ_mem γ⟩ y.1) (ψ.symm (γ • y.2))
    change f.1 (fun i => iotaQ γ * y.1 i) (ψ.symm (γ • y.2)) = f.1 y.1 (ψ.symm y.2)
    rw [h1]
    change f.1 y.1 ((iotaQ γ)⁻¹ • ψ.symm (γ • y.2)) = _
    rw [symm_smul ψ hψ, inv_smul_smul]⟩
  map_add' f g := rfl
  map_smul' c f := rfl

theorem modelToInv_apply (k : ℕ) (f : cochains N6 (functionRepresentation scalarTrivial X) k)
    (x : Fin (k + 1) → RationalGL3) (z : Z) :
    (modelToInv ψ hψ k f).1 (x, z) = f.1 x (ψ.symm z) := rfl

/-- The inverse construction: an invariant function gives a model cochain. -/
def invToModel (k : ℕ) :
    InvF RationalGL3 Z k →ₗ[ℂ] cochains N6 (functionRepresentation scalarTrivial X) k where
  toFun F := ⟨fun x e => F.1 (x, ψ e), by
    intro n x
    funext e
    obtain ⟨γ, hγ⟩ := exists_iotaQ_eq n.2
    have h := F.2 γ (x, ψ (n.val⁻¹ • e))
    have h1 : γ • ψ (n.val⁻¹ • e) = ψ e := by
      rw [← hψ, hγ, smul_inv_smul]
    change F.1 (fun i => n.val * x i, ψ e) = scalarTrivial n.val (F.1 (x, ψ (n.val⁻¹ • e)))
    have h2 : (γ • (x, ψ (n.val⁻¹ • e)) : (Fin (k + 1) → RationalGL3) × Z) =
        (fun i => n.val * x i, ψ e) := by
      refine Prod.ext ?_ h1
      funext i
      change iotaQ γ * x i = n.val * x i
      rw [hγ]
    rw [h2] at h
    rw [h]
    rfl⟩
  map_add' F G := rfl
  map_smul' c F := rfl

theorem invToModel_modelToInv (k : ℕ) (f : cochains N6 (functionRepresentation scalarTrivial X) k) :
    invToModel ψ hψ k (modelToInv ψ hψ k f) = f := by
  apply Subtype.ext
  funext x e
  change f.1 x (ψ.symm (ψ e)) = f.1 x e
  rw [Equiv.symm_apply_apply]

theorem modelToInv_invToModel (k : ℕ) (F : InvF RationalGL3 Z k) :
    modelToInv ψ hψ k (invToModel ψ hψ k F) = F := by
  apply Subtype.ext
  funext y
  change F.1 (y.1, ψ (ψ.symm y.2)) = F.1 y
  rw [Equiv.apply_symm_apply]

/-- Model cochains of `N6` are exactly the `Γ(6)`-invariant functions. -/
def modelInvEquiv (k : ℕ) :
    cochains N6 (functionRepresentation scalarTrivial X) k ≃ₗ[ℂ] InvF RationalGL3 Z k :=
  { modelToInv ψ hψ k with
    invFun := invToModel ψ hψ k
    left_inv := invToModel_modelToInv ψ hψ k
    right_inv := modelToInv_invToModel ψ hψ k }

end Model

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
