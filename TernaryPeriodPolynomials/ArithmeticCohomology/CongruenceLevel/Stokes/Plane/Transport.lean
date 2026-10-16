module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Terms
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.MackeyTheta

@[expose] public section


/-!
# From the subgroup `S_j ⊂ Γ(6)` to the plane group `Γ(6) ∩ h⁻¹ P h` (plane analogue of `LineTransport`)

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open MulAction

section ToKP

variable (i : PlaneFaces 6)

/-- The plane group of `Γ(6)` as a subgroup of `Γ(6)` versus as a subgroup of `SL₃(ℤ)`. -/
def planeSubEquiv : ↥(planeSub i) ≃* ↥(gammaNPAt 6 (planeFaceRepr i)) := Subgroup.subgroupOfEquivOfLe (show gammaNPAt 6 (planeFaceRepr i) ≤ gammaN 6 from fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)

theorem planeIncl_planeSubEquiv (s : ↥(planeSub i)) : planeIncl i (planeSubEquiv i s) = (planeSub i).subtype s := rfl

variable (σ : Rep ℂ ↥(gammaN 6))

theorem toKP_hT (g : ↥(gammaNPAt 6 (planeFaceRepr i))) (v : σ) :
    (Rep.res (planeSub i).subtype σ).ρ ((planeSubEquiv i).symm.toMonoidHom g) v = (Rep.res (planeIncl i) σ).ρ g v := rfl

/-- The transport `H²(S_i, Res σ) → H²(K_i, Res σ)` along `K_i ≅ S_i`. -/
def toKP : groupCohomology.H2 (Rep.res (planeSub i).subtype σ) →ₗ[ℂ] groupCohomology.H2 (Rep.res (planeIncl i) σ) :=
  EdgeNat.h2Map (planeSubEquiv i).symm.toMonoidHom (Rep.res (planeSub i).subtype σ) (Rep.res (planeIncl i) σ) LinearMap.id
    (fun g v => toKP_hT i σ g v)

theorem toKP_bijective : Function.Bijective (toKP i σ) := by
  have hid : Function.Bijective (LinearMap.id : (Rep.res (planeSub i).subtype σ) →ₗ[ℂ] (Rep.res (planeIncl i) σ)) :=
    Function.bijective_id
  exact ⟨EdgeNat.h2Map_injective _ _ _ _ _ (planeSubEquiv i).symm.bijective hid,
    EdgeNat.h2Map_surjective _ _ _ _ _ (planeSubEquiv i).symm.bijective hid⟩

theorem toKP_res (c : groupCohomology.H2 σ) :
    twoCohomologyRestriction (planeIncl i) σ c = toKP i σ (twoCohomologyRestriction (planeSub i).subtype σ c) := by
  unfold toKP
  rw [twoCohomologyRestriction_eq_h2Map, twoCohomologyRestriction_eq_h2Map, h2Map_comp]
  refine h2Map_congr ?_ _ _ _ _ (by ext; rfl) c
  ext k; rfl

theorem toKP_h2E (e : σ →ₗ[ℂ] σ)
    (hS : ∀ (k : ↥(planeSub i)) (v : σ), e ((Rep.res (planeSub i).subtype σ).ρ k v) = (Rep.res (planeSub i).subtype σ).ρ k (e v))
    (hK : ∀ (k : ↥(gammaNPAt 6 (planeFaceRepr i))) (v : σ), e ((Rep.res (planeIncl i) σ).ρ k v) = (Rep.res (planeIncl i) σ).ρ k (e v))
    (y : groupCohomology.H2 (Rep.res (planeSub i).subtype σ)) :
    h2E (Rep.res (planeIncl i) σ) e hK (toKP i σ y) = toKP i σ (h2E (Rep.res (planeSub i).subtype σ) e hS y) :=
  (h2Map_h2E (planeSubEquiv i).symm.toMonoidHom (Rep.res (planeSub i).subtype σ) (Rep.res (planeIncl i) σ) LinearMap.id
    (fun g v => toKP_hT i σ g v) e hS e hK (fun _ => rfl) y).symm


end ToKP

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
