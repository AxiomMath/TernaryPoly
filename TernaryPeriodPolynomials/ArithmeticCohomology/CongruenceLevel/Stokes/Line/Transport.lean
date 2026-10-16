module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Terms
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.MackeyTheta

@[expose] public section


/-!
# From the subgroup `S_i ⊂ Γ(6)` to the line group `Γ(6) ∩ i.rep⁻¹ Q i.rep`

Formalized by Claude Sonnet 5.5.

`lineSubEquiv i : ↥(lineSub i) ≃* ↥(gammaNQAt 6 i.rep)`; `toK` is the induced isomorphism `H²(S_i, Res_S σ) → H²(K_i, Res σ)` (pull-back along the inverse), compatible with restriction (`toK_res`), with the
coefficient endomorphisms `h2E` (`toK_h2E`), and carrying the vanishing of the restrictions to the flag stabilizers `lineFlagS i F` of `S_i` to that of `lineFlagStab 6 i.rep F`.
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

section ToK

variable (i : LineFaces 6)

/-- The line group of `Γ(6)` as a subgroup of `Γ(6)` versus as a subgroup of `SL₃(ℤ)`. -/
def lineSubEquiv : ↥(lineSub i) ≃* ↥(gammaNQAt 6 i.rep) := Subgroup.subgroupOfEquivOfLe (show gammaNQAt 6 i.rep ≤ gammaN 6 from fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)

theorem lineIncl_lineSubEquiv (s : ↥(lineSub i)) : lineIncl i (lineSubEquiv i s) = (lineSub i).subtype s := rfl

variable (σ : Rep ℂ ↥(gammaN 6))

theorem toK_hT (g : ↥(gammaNQAt 6 i.rep)) (v : σ) :
    (Rep.res (lineSub i).subtype σ).ρ ((lineSubEquiv i).symm.toMonoidHom g) v = (Rep.res (lineIncl i) σ).ρ g v := rfl

/-- The transport `H²(S_i, Res σ) → H²(K_i, Res σ)` along `K_i ≅ S_i`. -/
def toK : groupCohomology.H2 (Rep.res (lineSub i).subtype σ) →ₗ[ℂ] groupCohomology.H2 (Rep.res (lineIncl i) σ) :=
  EdgeNat.h2Map (lineSubEquiv i).symm.toMonoidHom (Rep.res (lineSub i).subtype σ) (Rep.res (lineIncl i) σ) LinearMap.id
    (fun g v => toK_hT i σ g v)

theorem toK_bijective : Function.Bijective (toK i σ) := by
  have hid : Function.Bijective (LinearMap.id : (Rep.res (lineSub i).subtype σ) →ₗ[ℂ] (Rep.res (lineIncl i) σ)) :=
    Function.bijective_id
  exact ⟨EdgeNat.h2Map_injective _ _ _ _ _ (lineSubEquiv i).symm.bijective hid,
    EdgeNat.h2Map_surjective _ _ _ _ _ (lineSubEquiv i).symm.bijective hid⟩

theorem toK_res (c : groupCohomology.H2 σ) :
    twoCohomologyRestriction (lineIncl i) σ c = toK i σ (twoCohomologyRestriction (lineSub i).subtype σ c) := by
  unfold toK
  rw [twoCohomologyRestriction_eq_h2Map, twoCohomologyRestriction_eq_h2Map, h2Map_comp]
  refine h2Map_congr ?_ _ _ _ _ (by ext; rfl) c
  ext k; rfl

theorem toK_h2E (e : σ →ₗ[ℂ] σ)
    (hS : ∀ (k : ↥(lineSub i)) (v : σ), e ((Rep.res (lineSub i).subtype σ).ρ k v) = (Rep.res (lineSub i).subtype σ).ρ k (e v))
    (hK : ∀ (k : ↥(gammaNQAt 6 i.rep)) (v : σ), e ((Rep.res (lineIncl i) σ).ρ k v) = (Rep.res (lineIncl i) σ).ρ k (e v))
    (y : groupCohomology.H2 (Rep.res (lineSub i).subtype σ)) :
    h2E (Rep.res (lineIncl i) σ) e hK (toK i σ y) = toK i σ (h2E (Rep.res (lineSub i).subtype σ) e hS y) :=
  (h2Map_h2E (lineSubEquiv i).symm.toMonoidHom (Rep.res (lineSub i).subtype σ) (Rep.res (lineIncl i) σ) LinearMap.id
    (fun g v => toK_hT i σ g v) e hS e hK (fun _ => rfl) y).symm

/-- The flag stabilizer of the frame `F` in `S_i`. -/
def lineFlagS (F : GL (Fin 2) ℚ) : Subgroup ↥(lineSub i) := (lineFlagStab 6 i.rep F).comap (lineSubEquiv i).toMonoidHom

/-- The isomorphism `lineFlagStab 6 i.rep F ≅ lineFlagS i F` induced by `K_i ≅ S_i`. -/
def flagPhi (F : GL (Fin 2) ℚ) : ↥(lineFlagStab 6 i.rep F) →* ↥(lineFlagS i F) :=
  (((lineSubEquiv i).symm.toMonoidHom).comp (lineFlagStab 6 i.rep F).subtype).codRestrict _ (fun k => by
    show lineSubEquiv i ((lineSubEquiv i).symm k.1) ∈ lineFlagStab 6 i.rep F
    simp only [MulEquiv.apply_symm_apply]; exact k.2)

theorem flagPhi_bijective (F : GL (Fin 2) ℚ) : Function.Bijective (flagPhi i F) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    have := congrArg (fun x : ↥(lineFlagS i F) => ((x : ↥(lineSub i))) ) hab
    exact (lineSubEquiv i).symm.injective this
  · intro s
    refine ⟨⟨lineSubEquiv i s.1, s.2⟩, ?_⟩
    apply Subtype.ext
    exact (lineSubEquiv i).symm_apply_apply s.1

theorem flagPhi_hT (F : GL (Fin 2) ℚ) (g : ↥(lineFlagStab 6 i.rep F)) (v : σ) :
    (Rep.res (lineFlagS i F).subtype (Rep.res (lineSub i).subtype σ)).ρ (flagPhi i F g) v =
      (Rep.res (lineFlagStab 6 i.rep F).subtype (Rep.res (lineIncl i) σ)).ρ g v := rfl

theorem toK_res_flag_eq (F : GL (Fin 2) ℚ) (y : groupCohomology.H2 (Rep.res (lineSub i).subtype σ)) :
    twoCohomologyRestriction (lineFlagStab 6 i.rep F).subtype (Rep.res (lineIncl i) σ) (toK i σ y) =
      EdgeNat.h2Map (flagPhi i F) (Rep.res (lineFlagS i F).subtype (Rep.res (lineSub i).subtype σ))
        (Rep.res (lineFlagStab 6 i.rep F).subtype (Rep.res (lineIncl i) σ)) LinearMap.id (fun g v => flagPhi_hT i σ F g v)
        (twoCohomologyRestriction (lineFlagS i F).subtype (Rep.res (lineSub i).subtype σ) y) := by
  have e1 := h2Map_comp (lineSubEquiv i).symm.toMonoidHom (lineFlagStab 6 i.rep F).subtype (Rep.res (lineSub i).subtype σ)
    (Rep.res (lineIncl i) σ) (Rep.res (lineFlagStab 6 i.rep F).subtype (Rep.res (lineIncl i) σ)) LinearMap.id
    (fun g v => toK_hT i σ g v) LinearMap.id (fun _ _ => rfl) y
  have e2 := h2Map_comp (lineFlagS i F).subtype (flagPhi i F) (Rep.res (lineSub i).subtype σ)
    (Rep.res (lineFlagS i F).subtype (Rep.res (lineSub i).subtype σ))
    (Rep.res (lineFlagStab 6 i.rep F).subtype (Rep.res (lineIncl i) σ)) LinearMap.id (fun _ _ => rfl) LinearMap.id
    (fun g v => flagPhi_hT i σ F g v) y
  rw [twoCohomologyRestriction_eq_h2Map, twoCohomologyRestriction_eq_h2Map]
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine h2Map_congr ?_ _ _ _ _ rfl y
  ext k; rfl

theorem toK_res_flag_iff (F : GL (Fin 2) ℚ) (y : groupCohomology.H2 (Rep.res (lineSub i).subtype σ)) :
    twoCohomologyRestriction (lineFlagStab 6 i.rep F).subtype (Rep.res (lineIncl i) σ) (toK i σ y) = 0 ↔
      twoCohomologyRestriction (lineFlagS i F).subtype (Rep.res (lineSub i).subtype σ) y = 0 := by
  rw [toK_res_flag_eq]
  have hid : Function.Bijective (LinearMap.id : σ →ₗ[ℂ] σ) := Function.bijective_id
  constructor
  · intro h
    refine (EdgeNat.h2Map_injective (flagPhi i F) (Rep.res (lineFlagS i F).subtype (Rep.res (lineSub i).subtype σ))
      (Rep.res (lineFlagStab 6 i.rep F).subtype (Rep.res (lineIncl i) σ)) LinearMap.id (fun g v => flagPhi_hT i σ F g v)
      (flagPhi_bijective i F) hid) ?_
    rw [h, map_zero]
  · intro h
    rw [h, map_zero]

end ToK

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
