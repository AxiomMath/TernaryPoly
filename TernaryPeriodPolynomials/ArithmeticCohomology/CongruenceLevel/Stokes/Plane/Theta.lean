module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Over
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Transport
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Theta

@[expose] public section


/-!
# The plane transport `Θ` and the identification of the orbit components of the induced class (plane analogue of `LineTheta`)

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section IdentGenP

variable {M : ℕ} [NeZero M] {i' : PlaneFaces M} (D : PlaneOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)

omit [NeZero M] in
/-- The pull-back identity: the pull-back of `c₀|_{Γ'}` along `μ` is the Mackey coordinate of the transport of `c₀`. -/
theorem PlaneOver.pullback_eq (c₀ : groupCohomology.H2 (Rep.of ρM)) :
    EdgeNat.h2Map D.mu (planeW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (planeSub D.i) D.u))
      (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M (planeFaceRepr i') hp)) (Rep.of ρM) c₀) =
    EdgeNat.h2Map (stabToAt (Δ6 M) (planeSub D.i) D.u) (Rep.of (ρ.comp (stabAt (Δ6 M) (planeSub D.i) D.u).subtype))
      (Rep.of (rhoStab ρ (Δ6 M) (planeSub D.i) D.u)) LinearMap.id (stabToAt_hT ρ (Δ6 M) (planeSub D.i) D.u)
      (EdgeNat.h2Map (kappa (Δ6 M) (stabAt (Δ6 M) (planeSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (planeSub D.i) D.u))
        (Rep.of (ρ.comp (Δ6 M).subtype)) (Rep.of (ρ.comp (stabAt (Δ6 M) (planeSub D.i) D.u).subtype))
        (ρ D.u) (kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) (planeSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (planeSub D.i) D.u))
        (transportΔ M ρ ρM hρ c₀)) := by
  have eT : transportΔ M ρ ρM hρ c₀ =
      EdgeNat.h2Map (eΔ M) (Rep.of ρM) (Rep.of (ρ.comp (Δ6 M).subtype)) LinearMap.id (eΔ_hT M ρ ρM hρ) c₀ := rfl
  have e1 := h2Map_comp (eΔ M) (kappa (Δ6 M) (stabAt (Δ6 M) (planeSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (planeSub D.i) D.u))
    (Rep.of ρM) (Rep.of (ρ.comp (Δ6 M).subtype))
    (Rep.of (ρ.comp (stabAt (Δ6 M) (planeSub D.i) D.u).subtype)) LinearMap.id
    (eΔ_hT M ρ ρM hρ) (ρ D.u)
    (kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) (planeSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (planeSub D.i) D.u)) c₀
  have e2 := h2Map_comp ((eΔ M).comp (kappa (Δ6 M) (stabAt (Δ6 M) (planeSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (planeSub D.i) D.u)))
    (stabToAt (Δ6 M) (planeSub D.i) D.u) (Rep.of ρM)
    (Rep.of (ρ.comp (stabAt (Δ6 M) (planeSub D.i) D.u).subtype))
    (Rep.of (rhoStab ρ (Δ6 M) (planeSub D.i) D.u))
    ((ρ D.u).comp LinearMap.id)
    (compHT (eΔ M) (kappa (Δ6 M) (stabAt (Δ6 M) (planeSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (planeSub D.i) D.u))
      (Rep.of ρM) (Rep.of (ρ.comp (Δ6 M).subtype))
      (Rep.of (ρ.comp (stabAt (Δ6 M) (planeSub D.i) D.u).subtype)) LinearMap.id
      (eΔ_hT M ρ ρM hρ) (ρ D.u)
      (kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) (planeSub D.i) D.u) D.u (stabAt_hu (Δ6 M) (planeSub D.i) D.u)))
    LinearMap.id (stabToAt_hT ρ (Δ6 M) (planeSub D.i) D.u) c₀
  have e3 := h2Map_comp (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M (planeFaceRepr i') hp)) D.mu (Rep.of ρM)
    (planeW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (planeSub D.i) D.u)) LinearMap.id (fun _ _ => rfl) (ρ (D.u : ↥(gammaN 6)))
    (D.hTgen ρ ρM hρ) c₀
  have hL : EdgeNat.h2Map D.mu (planeW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (planeSub D.i) D.u))
      (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M (planeFaceRepr i') hp)) (Rep.of ρM) c₀) = _ := e3
  refine hL.trans (Eq.trans ?_ (by rw [eT, e1, e2]))
  refine h2Map_congr ?_ _ _ _ _ ?_ c₀
  · ext s; rfl
  · ext w; rfl

omit [NeZero M] in
/-- **The `e_O`-component of the restriction to `S_i` of an induced class is `Θ` of the restriction of the level-`M` class** (coefficients `ρ`, `ρM`). -/
theorem PlaneOver.comp_eq (c₀ : groupCohomology.H2 (Rep.of ρM)) (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M))))
    (hcV : PhiH ρ (Δ6 M) cV = transportΔ M ρ ρM hρ c₀) :
    h2E (Rep.res (planeSub D.i).subtype (Rep.of (permRep ρ (Δ6 M)))) (eO (Δ6 M) (planeSub D.i) D.o)
      (fun k v => eO_equivariant ρ (Δ6 M) (planeSub D.i) D.o k v)
      (twoCohomologyRestriction (planeSub D.i).subtype (Rep.of (permRep ρ (Δ6 M))) cV) =
    D.thetaGen ρ ρM hρ (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M (planeFaceRepr i') hp)) (Rep.of ρM) c₀) := by
  unfold PlaneOver.thetaGen
  rw [← Theta_eq_orbit_component ρ (Δ6 M) (planeSub D.i) D.u (planeW i' ρM) D.mu (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)
    cV (transportΔ M ρ ρM hρ c₀) hcV _ (D.pullback_eq ρ ρM hρ c₀)]
  rw [← h2Hom_comp, h2Hom_eq_h2Map]
  unfold h2E
  refine h2Map_congr rfl _ _ _ _ ?_ _
  exact (eO_eq_qj (Δ6 M) (planeSub D.i) D.o (D.u : ↥(gammaN 6) ⧸ Δ6 M) D.hu).symm

end IdentGenP

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
