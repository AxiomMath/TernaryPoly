module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.TwistEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.FaceCanonical

@[expose] public section


/-!
# The Koszul pairing under a twisted isomorphism of extensions

Formalized by Claude Sonnet 5.5.

`radPairing_xi`: if `X : ext₂ ≅ ext₁` has radical map `φ` and `T : ρ₁ ≃ ρ₂`, then the Koszul pairings of the two radicals satisfy
`⟨Ξ x, Ξ' y⟩₂ = det(φ) ⟨x, y⟩₁`, where `Ξ, Ξ'` are the radical transports for `ρ` and for the contragredients (`dualEquiv T`).  This is the radical half of the orientation sign of a frame change.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

/-- **The Koszul value transforms by `det ψ`** under a change of the radical lattice together with isomorphisms of the coefficient modules. -/
theorem PhiC_xi {A₁ A₁' A₂ A₂' : Rep ℂ RadicalLattice} {e₁ : A₁ →ₗ[ℂ] A₁' →ₗ[ℂ] ℂ} {e₂ : A₂ →ₗ[ℂ] A₂' →ₗ[ℂ] ℂ}
    (he₁ : ∀ g a b, e₁ (A₁.ρ g a) (A₁'.ρ g b) = e₁ a b) (ψ : RadicalLattice →* RadicalLattice)
    (S : A₁ →ₗ[ℂ] A₂) (S' : A₁' →ₗ[ℂ] A₂')
    (hS' : ∀ r b, A₂'.ρ r (S' b) = S' (A₁'.ρ (ψ r) b))
    (hSe : ∀ a b, e₂ (S a) (S' b) = e₁ a b)
    (c : groupCohomology.cocycles₁ A₁) (c' : groupCohomology.cocycles₁ A₁')
    (d : groupCohomology.cocycles₁ A₂) (d' : groupCohomology.cocycles₁ A₂')
    (hd : ∀ r, d.1 r = S (c.1 (ψ r))) (hd' : ∀ r, d'.1 r = S' (c'.1 (ψ r))) :
    PhiC A₂ A₂' e₂ d d' = (radDet ψ : ℂ) * PhiC A₁ A₁' e₁ c c' := by
  have hcc := (groupCohomology.mem_cocycles₁_iff c.1).1 c.2
  have hcc' := (groupCohomology.mem_cocycles₁_iff c'.1).1 c'.2
  have step : ∀ u v : RadicalLattice,
      e₂ (d.1 u) (A₂'.ρ u (d'.1 v)) = e₁ (c.1 (ψ u)) (A₁'.ρ (ψ u) (c'.1 (ψ v))) := by
    intro u v
    rw [hd, hd', hS', hSe]
  have h1 : PhiC A₂ A₂' e₂ d d' = altForm A₁'.ρ e₁ c.1 c'.1 (ψ rl1) (ψ rl2) := by
    rw [PhiC_apply, step, step]
    rfl
  have hp : ψ rl1 = rl1 ^ (ψ rl1).toAdd.1 * rl2 ^ (ψ rl1).toAdd.2 := rl_decomp _
  have hq : ψ rl2 = rl1 ^ (ψ rl2).toAdd.1 * rl2 ^ (ψ rl2).toAdd.2 := rl_decomp _
  have key := altForm_gen he₁ hcc hcc' rl1 rl2 (ψ rl1).toAdd.1 (ψ rl1).toAdd.2 (ψ rl2).toAdd.1 (ψ rl2).toAdd.2
  rw [← hp, ← hq] at key
  rw [h1, key]
  simp only [radDet]
  push_cast
  rfl

variable {E₁ E₂ L : Type} [Group E₁] [Group E₂] [Group L]
  {ext₁ : GroupExtension RadicalLattice E₁ L} {ext₂ : GroupExtension RadicalLattice E₂ L}
  (X : TwistEquiv ext₂ ext₁) (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ ≃ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (X.θ g) v) = ρ₂.ρ g (T v))

/-- The contragredient isomorphism `E₁^* ≃ E₂^*` induced by `T`. -/
def dualEquiv : dualRepG ρ₁ ≃ₗ[ℂ] dualRepG ρ₂ := T.symm.dualMap

theorem dualEquiv_apply (φ : Module.Dual ℂ ρ₁) (v : ρ₂) : dualEquiv ρ₁ ρ₂ T φ v = φ (T.symm v) := rfl

include hT in
theorem hTdual (g : E₂) (φ : Module.Dual ℂ ρ₁) :
    dualEquiv ρ₁ ρ₂ T ((dualRepG ρ₁).ρ (X.θ g) φ) = (dualRepG ρ₂).ρ g (dualEquiv ρ₁ ρ₂ T φ) := by
  apply LinearMap.ext
  intro v
  rw [dualEquiv_apply, dualRepG_inv, dualRepG_inv, dualEquiv_apply]
  congr 1
  apply T.injective
  rw [LinearEquiv.apply_symm_apply, ← map_inv X.θ g, hT, LinearEquiv.apply_symm_apply]


variable [FiniteDimensional ℂ ρ₁] [FiniteDimensional ℂ ρ₂]

/-- **The Koszul pairing of the radical changes by `det φ`** under a twisted isomorphism of extensions. -/
theorem radPairing_xi (x : groupCohomology.H1 (Rep.res ext₁.inl ρ₁))
    (y : groupCohomology.H1 (Rep.res ext₁.inl (dualRepG ρ₁))) :
    radPairingOf (ext := ext₂) (perfectInv_dual ρ₂) (radXi X ρ₁ ρ₂ T hT x)
        (radXi X (dualRepG ρ₁) (dualRepG ρ₂) (dualEquiv ρ₁ ρ₂ T) (hTdual X ρ₁ ρ₂ T hT) y) =
      (radDet X.φ.toMonoidHom : ℂ) * radPairingOf (ext := ext₁) (perfectInv_dual ρ₁) x y := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    induction y using groupCohomology.H1_induction_on with
    | h c' =>
      rw [radXi_π, radXi_π, radPairingOf_spec, radPairingOf_spec]
      refine PhiC_xi (A₁ := Rep.res ext₁.inl ρ₁) (A₁' := Rep.res ext₁.inl (dualRepG ρ₁))
        (A₂ := Rep.res ext₂.inl ρ₂) (A₂' := Rep.res ext₂.inl (dualRepG ρ₂))
        (e₁ := Module.Dual.eval ℂ ρ₁) (e₂ := Module.Dual.eval ℂ ρ₂)
        (fun g a b => (perfectInv_dual ρ₁).inv (ext₁.inl g) a b) X.φ.toMonoidHom T.toLinearMap
        (dualEquiv ρ₁ ρ₂ T).toLinearMap (fun r b => ?_) (fun a b => ?_) c c' _ _ (fun r => rfl) (fun r => rfl)
      · change (dualRepG ρ₂).ρ (ext₂.inl r) (dualEquiv ρ₁ ρ₂ T b) =
          dualEquiv ρ₁ ρ₂ T ((dualRepG ρ₁).ρ (ext₁.inl (X.φ r)) b)
        rw [← X.inl_comm]
        exact (hTdual X ρ₁ ρ₂ T hT (ext₂.inl r) b).symm
      · change dualEquiv ρ₁ ρ₂ T b (T a) = b a
        rw [dualEquiv_apply, LinearEquiv.symm_apply_apply]

end TernaryPeriodPolynomials.Argument.FrameInvariance
