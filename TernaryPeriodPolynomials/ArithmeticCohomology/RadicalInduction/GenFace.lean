module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.CanIdent
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.MackeyEdge

@[expose] public section


/-!
# The face group `S = K ∩ Γ(6)`, the conjugation `μ` and the transport `toKgen`, for an arbitrary subgroup `K ≤ Γ(6)` of `SL₃(ℤ)`

Formalized by Claude Sonnet 5.5.

Generic versions (for a subgroup `K` of `SL₃(ℤ)` contained in `Γ(6)`, and `K' ≤ Γ(M)`, `u ∈ Γ(6)`) of the line/plane objects of `GammaNStokes`: `SK K = K.subgroupOf Γ(6)`, `eSK : S ≃ K`, `toKgen`,
the conjugation `muGen : Stab_S(uΔ) → K'`, `s ↦ u⁻¹ s u`, its equivariance `hTgen`, and the identification of its pull-back with the Mackey coordinate (`pullback_eq_gen`).
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section Gen

variable (K : Subgroup SL(3, ℤ)) (hK : K ≤ gammaN 6)

/-- The face group as a subgroup of `Γ(6)`. -/
abbrev SK : Subgroup ↥(gammaN 6) := K.subgroupOf (gammaN 6)

/-- `S ≃ K`. -/
def eSK : ↥(SK K) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hK

/-- The inclusion `K ≤ Γ(6)`. -/
abbrev inclK : ↥K →* ↥(gammaN 6) := Subgroup.inclusion hK

variable (σ : Rep ℂ ↥(gammaN 6))

theorem toKgen_hT (g : ↥K) (v : σ) :
    (Rep.res (SK K).subtype σ).ρ ((eSK K hK).symm.toMonoidHom g) v = (Rep.res (inclK K hK) σ).ρ g v := rfl

/-- The transport `H²(S, Res σ) → H²(K, Res σ)`. -/
def toKgen : groupCohomology.H2 (Rep.res (SK K).subtype σ) →ₗ[ℂ] groupCohomology.H2 (Rep.res (inclK K hK) σ) :=
  EdgeNat.h2Map (eSK K hK).symm.toMonoidHom (Rep.res (SK K).subtype σ) (Rep.res (inclK K hK) σ) LinearMap.id
    (fun g v => toKgen_hT K hK σ g v)

theorem toKgen_res (c : groupCohomology.H2 σ) :
    twoCohomologyRestriction (inclK K hK) σ c = toKgen K hK σ (twoCohomologyRestriction (SK K).subtype σ c) := by
  unfold toKgen
  rw [twoCohomologyRestriction_eq_h2Map, twoCohomologyRestriction_eq_h2Map, h2Map_comp]
  refine h2Map_congr ?_ _ _ _ _ (by ext; rfl) c
  ext k; rfl

theorem toKgen_h2E (e : σ →ₗ[ℂ] σ)
    (hS : ∀ (k : ↥(SK K)) (v : σ), e ((Rep.res (SK K).subtype σ).ρ k v) = (Rep.res (SK K).subtype σ).ρ k (e v))
    (hKK : ∀ (k : ↥K) (v : σ), e ((Rep.res (inclK K hK) σ).ρ k v) = (Rep.res (inclK K hK) σ).ρ k (e v))
    (y : groupCohomology.H2 (Rep.res (SK K).subtype σ)) :
    h2E (Rep.res (inclK K hK) σ) e hKK (toKgen K hK σ y) = toKgen K hK σ (h2E (Rep.res (SK K).subtype σ) e hS y) :=
  (h2Map_h2E (eSK K hK).symm.toMonoidHom (Rep.res (SK K).subtype σ) (Rep.res (inclK K hK) σ) LinearMap.id
    (fun g v => toKgen_hT K hK σ g v) e hS e hKK (fun _ => rfl) y).symm

end Gen

end TernaryPeriodPolynomials.Argument.RadicalInduction
