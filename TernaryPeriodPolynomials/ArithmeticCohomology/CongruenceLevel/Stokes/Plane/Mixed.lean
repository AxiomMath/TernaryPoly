module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Pairing2
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Flag

@[expose] public section


/-!
# Forward mixedness of the plane transports

Formalized by Claude Sonnet 5.5.

`PlaneOver.JEP_mem_mixed` and `PlaneOver.JDP_mem_mixed`: the plane transports `JEP`, `JDP` send classes vanishing on every flag group of the plane face `j'` of `Γ(M)` (for `JDP`: classes whose literal image `toLitP` does) to classes of `planeMixedSub` of the plane face `j` of `Γ(6)`.
Equivalently `planeMixedAt ≤ UE` and the mixed duals lie in `UD`; the plane analogue of `LineOver.JEraw_mem`/`JDraw_mem`.
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
open TernaryPeriodPolynomials.Argument.EisensteinClass

section PlaneMixed

variable {M : ℕ} [NeZero M] (n : ℕ) {j' : PlaneFaces M} (D : PlaneOver M j')

theorem PlaneOver.JEP_mem_mixed (ε : groupCohomology.H2 (faceRep M (planeFaceRepr j') n))
    (hε : ε ∈ planeMixedAt M (planeFaceRepr j') (faceRep M (planeFaceRepr j') n)) :
    D.JEP n ε ∈ planeMixedSub (permRep (rhoEn n) (Δ6 M)) D.i :=
  (Submodule.mem_iInf _).2 fun F₀ => LinearMap.mem_ker.2
    (D.thetaGen_flag_zero (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) ε
      (fun F'' => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hε F'')) F₀)

theorem PlaneOver.JDP_mem_mixed
    (ε' : groupCohomology.H2 (Rep.of ((dualRhoC M n).comp (Subgroup.inclusion (gammaNPAt_le M (planeFaceRepr j'))))))
    (hε' : toLitP (M := M) n (planeFaceRepr j') ε' ∈ planeMixedAt M (planeFaceRepr j') (dualRepG (faceRep M (planeFaceRepr j') n))) :
    D.JDP n ε' ∈ planeMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i := by
  refine (Submodule.mem_iInf _).2 fun F₀ => LinearMap.mem_ker.2 ?_
  refine (toKP_res_flag_iff D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) F₀ _).mpr ?_
  refine res_h2Hom_zero (planeFlagS D.i F₀).subtype ((Rep.resFunctor (planeSub D.i).subtype).map (dualRepHom (rhoEn n) (Δ6 M))) _ ?_
  exact (toKP_res_flag_iff D.i (Rep.of (permRep (rhoEn n).dual (Δ6 M))) F₀ _).mp
    (D.thetaGen_flag_zero (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLitP (M := M) n (planeFaceRepr j') ε')
      (fun F'' => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hε' F'')) F₀)

theorem PlaneOver.planeMixedAt_le_UE :
    planeMixedAt M (planeFaceRepr j') (faceRep M (planeFaceRepr j') n) ≤ D.UE n :=
  fun ε hε => D.JEP_mem_mixed n ε hε

end PlaneMixed

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
