module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Theta
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Pairing1

@[expose] public section


/-!
# The plane orbit components (plane analogue of `LinePairing1.termX_eq`, `termY_eq`)

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section Part3P

variable {M : ℕ} [NeZero M] {i' : PlaneFaces M} (D : PlaneOver M i') (n : ℕ)


omit [NeZero M] in
theorem eO_dual_equivariantP {i' : PlaneFaces M} (D : PlaneOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ ↥(gammaN 6) E) (k : ↥(gammaNPAt 6 (planeFaceRepr D.i))) (f : Module.Dual ℂ ((↥(gammaN 6) ⧸ Δ6 M) → E)) :
    (eO (Δ6 M) (planeSub D.i) D.o).dualMap ((Rep.res (planeIncl D.i) (Rep.of (permRep ρ (Δ6 M)).dual)).ρ k f) =
      (Rep.res (planeIncl D.i) (Rep.of (permRep ρ (Δ6 M)).dual)).ρ k ((eO (Δ6 M) (planeSub D.i) D.o).dualMap f) :=
  eO_dual_equivariant ρ (Δ6 M) (planeSub D.i) D.o ((planeSubEquiv D.i).symm k) f

theorem PlaneOver.termX_eq (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀)
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀) :
    (planeTermX c₀ hz cV hcV D.i D.o).1 =
      toKP D.i (Rep.of (permRep (rhoEn n) (Δ6 M)))
        (D.thetaGen (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) (rPlane M n (planeFaceRepr i') c₀)) := by
  have hS : ∀ (k : ↥(planeSub D.i)) (v : (↥(gammaN 6) ⧸ Δ6 M) → GeneralEisenstein.HomogeneousPoly n),
      eO (Δ6 M) (planeSub D.i) D.o ((Rep.res (planeSub D.i).subtype (Rep.of (permRep (rhoEn n) (Δ6 M)))).ρ k v) =
        (Rep.res (planeSub D.i).subtype (Rep.of (permRep (rhoEn n) (Δ6 M)))).ρ k (eO (Δ6 M) (planeSub D.i) D.o v) :=
    fun k v => eO_equivariant (rhoEn n) (Δ6 M) (planeSub D.i) D.o k v
  have h1 : (planeTermX c₀ hz cV hcV D.i D.o).1 =
      h2E (Rep.res (planeIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)))) (eO (Δ6 M) (planeSub D.i) D.o)
        (fun k v => eO_plane_equivariant (rhoEn n) (Δ6 M) D.i D.o k v)
        (toKP D.i (Rep.of (permRep (rhoEn n) (Δ6 M)))
          (twoCohomologyRestriction (planeSub D.i).subtype (Rep.of (permRep (rhoEn n) (Δ6 M))) cV)) := by
    rw [← toKP_res]; rfl
  rw [h1, toKP_h2E D.i (Rep.of (permRep (rhoEn n) (Δ6 M))) (eO (Δ6 M) (planeSub D.i) D.o) hS
    (fun k v => eO_plane_equivariant (rhoEn n) (Δ6 M) D.i D.o k v)]
  congr 1
  exact D.comp_eq (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀ cV hcV

theorem PlaneOver.termY_eq (c₀' : groupCohomology.H2 (gammaNRepAllDual M n)) (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c₀')
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) c₀') :
    (planeTermY c₀' hz' cVd hcVd D.i D.o).1 =
      toKP D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)
        (dualPushG (rhoEn n) (Δ6 M) (planeSub D.i)
          (D.thetaGen (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
            (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M (planeFaceRepr i') hp)) (gammaNRepAllDual M n) c₀'))) := by
  have hS : ∀ (k : ↥(planeSub D.i)) (v : Module.Dual ℂ ((↥(gammaN 6) ⧸ Δ6 M) → GeneralEisenstein.HomogeneousPoly n)),
      (eO (Δ6 M) (planeSub D.i) D.o).dualMap ((Rep.res (planeSub D.i).subtype (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)).ρ k v) =
        (Rep.res (planeSub D.i).subtype (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)).ρ k ((eO (Δ6 M) (planeSub D.i) D.o).dualMap v) :=
    fun k v => eO_dual_equivariant (rhoEn n) (Δ6 M) (planeSub D.i) D.o k v
  have h1 : (planeTermY c₀' hz' cVd hcVd D.i D.o).1 =
      h2E (Rep.res (planeIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)) (eO (Δ6 M) (planeSub D.i) D.o).dualMap
        (fun k v => eO_dual_equivariantP D (rhoEn n) k v)
        (toKP D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)
          (dualPushG (rhoEn n) (Δ6 M) (planeSub D.i) (twoCohomologyRestriction (planeSub D.i).subtype (Rep.of (permRep (rhoEn n).dual (Δ6 M))) cVd))) := by
    have e := toKP_res D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) (h2Hom (dualRepHom (rhoEn n) (Δ6 M)) cVd)
    have e2 := res_h2Hom_eq (planeSub D.i).subtype (dualRepHom (rhoEn n) (Δ6 M)) cVd
    unfold planeTermY
    change h2E _ _ _ (twoCohomologyRestriction (planeIncl D.i) _ _) = _
    rw [e, e2]; rfl
  rw [h1, toKP_h2E D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) (eO (Δ6 M) (planeSub D.i) D.o).dualMap hS
    (fun k v => eO_dual_equivariantP D (rhoEn n) k v), h2E_dualPushG (rhoEn n) (Δ6 M) (planeSub D.i) D.o hS]
  congr 2
  exact D.comp_eq (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) c₀' cVd hcVd

end Part3P

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
