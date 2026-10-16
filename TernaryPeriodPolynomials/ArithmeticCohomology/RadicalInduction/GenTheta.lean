module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenCup
public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.Main

@[expose] public section


/-!
# The map on `H¹` induced by a comparison `φ : Res V₁ ⟶ V`, on classes of twisted cusp functions

Formalized by Claude Sonnet 5.5.

For `Γ(M) ≤ Γ(N)`, a `Γ(N)`-module `V₁`, a `Γ(M)`-module `V` and a `Γ(M)`-morphism `φ : Res V₁ ⟶ V`:
`mapH1 φ = H¹(incl, φ)`, `phiTw φ : Tw(V₁) → Tw(V)`, `Φ ↦ φ ∘ Φ`, and `mapH1_theta`: `θ_M (mapH1 φ x) = mTw (φ ∘ Φ)` whenever `θ_N x = mTw Φ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

variable {N M : ℕ} [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) (hle : Gamma M ≤ Gamma N) {V₁ : Rep ℂ (Gamma N)} {V : Rep ℂ (Gamma M)}
  (φ : Rep.res (Subgroup.inclusion hle) V₁ ⟶ V)

/-- The map on `H¹` induced by `φ`. -/
def mapH1 : groupCohomology.H1 V₁ →ₗ[ℂ] groupCohomology.H1 V :=
  (groupCohomology.map (Subgroup.inclusion hle) φ 1).hom

theorem phi_incl (g : gammaNGL M) (a : V₁) :
    φ.hom ((transRep hN.out V₁).ρ (inclGL hM hle g) a) = (transRep hM V).ρ g (φ.hom a) := by
  have h := Rep.hom_comm_apply φ ((gammaEquiv hM).symm g) a
  exact h

/-- `φ ∘ Φ` is a twisted cusp function for `Γ(M)`. -/
theorem phiTw_mem (Φ : RationalLine2 → V₁) (hΦ : Φ ∈ Tw (transRep hN.out V₁).ρ) :
    (fun c => φ.hom (Φ c)) ∈ Tw (transRep hM V).ρ := by
  obtain ⟨f, hf, htw⟩ := hΦ
  refine ⟨fun g => φ.hom (f (inclGL hM hle g)), fun g h => ?_, fun γ x => ?_⟩
  · have := hf (inclGL hM hle g) (inclGL hM hle h)
    rw [← map_mul] at this
    change φ.hom (f (inclGL hM hle (g * h))) = _
    rw [this, map_add, phi_incl hM hle φ g]
  · have := htw (inclGL hM hle γ) x
    change φ.hom (Φ ((inclGL hM hle γ : gammaNGL N) • x)) = _
    rw [this, map_add, phi_incl hM hle φ γ]

/-- `φ ∘ Φ` as an element of `Tw`. -/
def phiTw (Φ : Tw (transRep hN.out V₁).ρ) : Tw (transRep hM V).ρ := ⟨fun c => φ.hom (Φ.1 c), phiTw_mem hM hle φ Φ.1 Φ.2⟩

theorem fTw_phi (Φ : Tw (transRep hN.out V₁).ρ) (g : gammaNGL M) :
    fTw (transRep hM V) (phiTw hM hle φ Φ).1 g = φ.hom (fTw (transRep hN.out V₁) Φ.1 (inclGL hM hle g)) := by
  unfold fTw
  change φ.hom (Φ.1 ((g : IntegralGL) • cusp1)) - _ = φ.hom (Φ.1 ((inclGL hM hle g : gammaNGL N) • cusp1) -
    (transRep hN.out V₁).ρ (inclGL hM hle g) (Φ.1 cusp1))
  rw [map_sub, phi_incl hM hle φ g]
  rfl

theorem mapH1_theta (Φ : Tw (transRep hN.out V₁).ρ) (x : groupCohomology.H1 V₁)
    (hx : (thetaIso hN.out V₁).hom.hom x = mTw (transRep hN.out V₁) Φ) :
    (thetaIso hM V).hom.hom (mapH1 hle φ x) = mTw (transRep hM V) (phiTw hM hle φ Φ) := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    obtain ⟨c', hc', hθ⟩ := thetaIso_hom_π hN.out V₁ c
    rw [hθ, mTw_apply] at hx
    obtain ⟨w, hw⟩ := (H1π_eq_iff_gen _ _ _).1 hx
    unfold mapH1
    rw [groupCohomology.H1π_comp_map_apply]
    obtain ⟨c'', hc'', hθ'⟩ := thetaIso_hom_π hM V (groupCohomology.mapCocycles₁ (Subgroup.inclusion hle) φ c)
    rw [hθ', mTw_apply]
    refine (H1π_eq_iff_gen _ _ _).2 ⟨φ.hom w, fun g => ?_⟩
    have h1 := congrArg φ.hom (hw (inclGL hM hle g))
    have h2 : c'.1 (inclGL hM hle g) = c.1 (Subgroup.inclusion hle ((gammaEquiv hM).symm g)) := by
      rw [hc', symm_incl hN.out hM hle g]
    have e1 : c''.1 g = φ.hom (c'.1 (inclGL hM hle g)) := by
      rw [hc'', h2]
      rfl
    change c''.1 g - fTw (transRep hM V) (phiTw hM hle φ Φ).1 g = _
    rw [fTw_phi hM hle φ Φ g, e1, ← map_sub]
    refine h1.trans ?_
    rw [map_sub, phi_incl hM hle φ g]

end TernaryPeriodPolynomials.Argument.RadicalInduction
