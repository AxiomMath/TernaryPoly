module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenMu

@[expose] public section


/-!
# The `e_O`-component of the restriction of an induced class, at an arbitrary frame

Formalized by Claude Sonnet 5.5.

Generic versions of `LineOver.pullback_eq` and `LineOver.comp_eq`: the pull-back of `res_{K'} c₀` along `μ` is the Mackey coordinate of the transport of `c₀` (`pullback_eq_gen`), hence the `e_O`-component of
`res_S c_V` is `Θ(res_{K'} c₀)` (`comp_eq_gen`).
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

section Comp

variable {M : ℕ} [NeZero M] (K K' : Subgroup SL(3, ℤ)) (u : ↥(gammaN 6))
  (hmem : ∀ s : ↥(SK K), (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ gammaN M →
    (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ K')
  {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)
  (hK' : K' ≤ gammaN M)

omit [NeZero M] in
/-- **The pull-back of `c₀|_{K'}` along `μ` is the Mackey coordinate of the transport of `c₀`.** -/
theorem pullback_eq_gen (c₀ : groupCohomology.H2 (Rep.of ρM)) :
    EdgeNat.h2Map (muGen K K' u hmem) (WK K' ρM hK') (Rep.of (rhoStab ρ (Δ6 M) (SK K) u))
      (ρ (u : ↥(gammaN 6))) (hTgen K K' u hmem ρ ρM hρ hK')
      (twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀) =
    EdgeNat.h2Map (stabToAt (Δ6 M) (SK K) u) (Rep.of (ρ.comp (stabAt (Δ6 M) (SK K) u).subtype))
      (Rep.of (rhoStab ρ (Δ6 M) (SK K) u)) LinearMap.id (stabToAt_hT ρ (Δ6 M) (SK K) u)
      (EdgeNat.h2Map (kappa (Δ6 M) (stabAt (Δ6 M) (SK K) u) u (stabAt_hu (Δ6 M) (SK K) u))
        (Rep.of (ρ.comp (Δ6 M).subtype)) (Rep.of (ρ.comp (stabAt (Δ6 M) (SK K) u).subtype))
        (ρ u) (kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) (SK K) u) u (stabAt_hu (Δ6 M) (SK K) u))
        (transportΔ M ρ ρM hρ c₀)) := by
  have eT : transportΔ M ρ ρM hρ c₀ =
      EdgeNat.h2Map (eΔ M) (Rep.of ρM) (Rep.of (ρ.comp (Δ6 M).subtype)) LinearMap.id (eΔ_hT M ρ ρM hρ) c₀ := rfl
  have e1 := h2Map_comp (eΔ M) (kappa (Δ6 M) (stabAt (Δ6 M) (SK K) u) u (stabAt_hu (Δ6 M) (SK K) u))
    (Rep.of ρM) (Rep.of (ρ.comp (Δ6 M).subtype))
    (Rep.of (ρ.comp (stabAt (Δ6 M) (SK K) u).subtype)) LinearMap.id
    (eΔ_hT M ρ ρM hρ) (ρ u)
    (kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) (SK K) u) u (stabAt_hu (Δ6 M) (SK K) u)) c₀
  have e2 := h2Map_comp ((eΔ M).comp (kappa (Δ6 M) (stabAt (Δ6 M) (SK K) u) u (stabAt_hu (Δ6 M) (SK K) u)))
    (stabToAt (Δ6 M) (SK K) u) (Rep.of ρM)
    (Rep.of (ρ.comp (stabAt (Δ6 M) (SK K) u).subtype))
    (Rep.of (rhoStab ρ (Δ6 M) (SK K) u))
    ((ρ u).comp LinearMap.id)
    (compHT (eΔ M) (kappa (Δ6 M) (stabAt (Δ6 M) (SK K) u) u (stabAt_hu (Δ6 M) (SK K) u))
      (Rep.of ρM) (Rep.of (ρ.comp (Δ6 M).subtype))
      (Rep.of (ρ.comp (stabAt (Δ6 M) (SK K) u).subtype)) LinearMap.id
      (eΔ_hT M ρ ρM hρ) (ρ u)
      (kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) (SK K) u) u (stabAt_hu (Δ6 M) (SK K) u)))
    LinearMap.id (stabToAt_hT ρ (Δ6 M) (SK K) u) c₀
  have e3 := h2Map_comp (Subgroup.inclusion hK') (muGen K K' u hmem) (Rep.of ρM)
    (WK K' ρM hK') (Rep.of (rhoStab ρ (Δ6 M) (SK K) u)) LinearMap.id (fun _ _ => rfl) (ρ (u : ↥(gammaN 6)))
    (hTgen K K' u hmem ρ ρM hρ hK') c₀
  have hL : EdgeNat.h2Map (muGen K K' u hmem) (WK K' ρM hK') (Rep.of (rhoStab ρ (Δ6 M) (SK K) u))
      (ρ (u : ↥(gammaN 6))) (hTgen K K' u hmem ρ ρM hρ hK')
      (twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀) = _ := e3
  refine hL.trans (Eq.trans ?_ (by rw [eT, e1, e2]))
  refine h2Map_congr ?_ _ _ _ _ ?_ c₀
  · ext s; rfl
  · ext w; rfl

omit [NeZero M] in
/-- **The `e_O`-component of the restriction to `S` of an induced class is `Θ` of the restriction of the level-`M` class.** -/
theorem comp_eq_gen (o : orbitRel.Quotient ↥(SK K) (↥(gammaN 6) ⧸ Δ6 M))
    (hu : (u : ↥(gammaN 6) ⧸ Δ6 M) = Quotient.out o)
    (c₀ : groupCohomology.H2 (Rep.of ρM)) (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M))))
    (hcV : PhiH ρ (Δ6 M) cV = transportΔ M ρ ρM hρ c₀) :
    h2E (Rep.res (SK K).subtype (Rep.of (permRep ρ (Δ6 M)))) (eO (Δ6 M) (SK K) o)
      (fun k v => eO_equivariant ρ (Δ6 M) (SK K) o k v)
      (twoCohomologyRestriction (SK K).subtype (Rep.of (permRep ρ (Δ6 M))) cV) =
    Theta ρ (Δ6 M) (SK K) u (WK K' ρM hK') (muGen K K' u hmem) (ρ (u : ↥(gammaN 6))) (hTgen K K' u hmem ρ ρM hρ hK')
      (twoCohomologyRestriction (Subgroup.inclusion hK') (Rep.of ρM) c₀) := by
  rw [← Theta_eq_orbit_component ρ (Δ6 M) (SK K) u (WK K' ρM hK') (muGen K K' u hmem) (ρ (u : ↥(gammaN 6)))
    (hTgen K K' u hmem ρ ρM hρ hK') cV (transportΔ M ρ ρM hρ c₀) hcV _ (pullback_eq_gen K K' u hmem ρ ρM hρ hK' c₀)]
  rw [← h2Hom_comp, h2Hom_eq_h2Map]
  unfold h2E
  refine h2Map_congr rfl _ _ _ _ ?_ _
  exact (eO_eq_qj (Δ6 M) (SK K) o (u : ↥(gammaN 6) ⧸ Δ6 M) hu).symm

end Comp

end TernaryPeriodPolynomials.Argument.RadicalInduction
