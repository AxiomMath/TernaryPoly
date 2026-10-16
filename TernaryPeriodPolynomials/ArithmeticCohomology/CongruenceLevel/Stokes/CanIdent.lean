module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cone.AssemblyEx

@[expose] public section


/-!
# The literal identification of the orbit components with the canonical pairing of `Γ(M)`: `LineCanIdent`, `PlaneCanIdent`

Formalized by Claude Sonnet 5.5.

`LineCanIdent M n hM h6` says: for a line face `i'` of `Γ(M)` over `(i, O)` (the chosen data `lineOverOf h6 i'`, `i'.rep = q · i.rep · u'`) and mixed classes `ε` (coefficients `E_n`), `ε'` (coefficients `E_n^*`) of the line
group of `i'`, the level-6 canonical pairing `can6` (the `facePairingCan` on the Hochschild-Serre edges) of the Mackey transports `Θ(ε)`, `Θ'(ε')` — classes of the `e_O`-component of the induced module
`Fun(Γ(6)/Γ(M), E_n)` — equals the level-`M` canonical pairing `canAt` of `ε`, `ε'`.  It is the content of Step 2 (compatibility with finite-index induction, including the Koszul pairing of the radical lattices of index
`(M/6)²`) together with Step 1b (the frame `i'.rep = q · i.rep · u'`); the exact value, with no constant, is claimed.  `PlaneCanIdent` is the plane analogue.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction
open TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.Argument.EisensteinDual

section CanIdent

variable {M : ℕ} [NeZero M] (n : ℕ) {i' : LineFaces M} (D : LineOver M i')

/-- The transport of a mixed class `ε` of the line group of `i'` (coefficients `E_n`) to a mixed class of the line group of `i` for the induced module. -/
def LineOver.JEm (ε : groupCohomology.H2 (lineFaceRep M i'.rep n)) (hε : ε ∈ lineMixedAt M i'.rep (lineFaceRep M i'.rep n)) :
    lineMixedSub (permRep (rhoEn n) (Δ6 M)) D.i :=
  ⟨toK D.i (Rep.of (permRep (rhoEn n) (Δ6 M))) (D.thetaGen (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) ε),
    (Submodule.mem_iInf _).2 fun F₀ => LinearMap.mem_ker.2
      (D.thetaGen_flag_zero (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) ε
        (fun F'' => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hε F'')) F₀)⟩

/-- The transport of a mixed class `ε'` of the line group of `i'` (coefficients `E_n^*`) to a mixed class of the line group of `i` for the dual induced module. -/
def LineOver.JDm (ε' : groupCohomology.H2 (dualRepG (lineFaceRep M i'.rep n))) (hε' : ε' ∈ lineMixedAt M i'.rep (dualRepG (lineFaceRep M i'.rep n))) :
    lineMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i :=
  ⟨toK D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) (dualPushG (rhoEn n) (Δ6 M) (lineSub D.i)
      (D.thetaGen (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) ε')),
    (Submodule.mem_iInf _).2 fun F₀ => LinearMap.mem_ker.2 (by
      refine (toK_res_flag_iff D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) F₀ _).mpr ?_
      refine res_h2Hom_zero (lineFlagS D.i F₀).subtype ((Rep.resFunctor (lineSub D.i).subtype).map (dualRepHom (rhoEn n) (Δ6 M))) _ ?_
      exact (toK_res_flag_iff D.i (Rep.of (permRep (rhoEn n).dual (Δ6 M))) F₀ _).mp
        (D.thetaGen_flag_zero (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) ε'
          (fun F'' => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hε' F'')) F₀))⟩

end CanIdent

def LineCanIdent (M n : ℕ) [NeZero M] (hM : 3 ≤ M) (h6 : 6 ∣ M) : Prop :=
  ∀ (i' : LineFaces M) (ε : groupCohomology.H2 (lineFaceRep M i'.rep n))
    (hε : ε ∈ lineMixedAt M i'.rep (lineFaceRep M i'.rep n))
    (ε' : groupCohomology.H2 (dualRepG (lineFaceRep M i'.rep n)))
    (hε' : ε' ∈ lineMixedAt M i'.rep (dualRepG (lineFaceRep M i'.rep n))),
      can6 (permRep (rhoEn n) (Δ6 M)) (lineOverOf h6 i').i ((lineOverOf h6 i').JEm n ε hε) ((lineOverOf h6 i').JDm n ε' hε') =
        canAt M i'.rep hM (lineFaceRep M i'.rep n) ⟨ε, hε⟩ ⟨ε', hε'⟩

/-- The plane statement at one plane face over `(j, O)` (data `D`). -/
def PlaneCanIdentAt {M : ℕ} [NeZero M] (n : ℕ) (hM : 3 ≤ M) {j' : PlaneFaces M} (D : PlaneOver M j') : Prop :=
  ∀ (ε : groupCohomology.H2 (faceRep M (planeFaceRepr j') n))
    (hε : ε ∈ planeMixedAt M (planeFaceRepr j') (faceRep M (planeFaceRepr j') n))
    (ε' : groupCohomology.H2 (Rep.of ((dualRhoC M n).comp (Subgroup.inclusion (gammaNPAt_le M (planeFaceRepr j'))))))
    (hε' : toLitP (M := M) n (planeFaceRepr j') ε' ∈ planeMixedAt M (planeFaceRepr j') (dualRepG (faceRep M (planeFaceRepr j') n)))
    (x : planeMixedSub (permRep (rhoEn n) (Δ6 M)) D.i) (y : planeMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i),
    x.1 = D.JEP n ε → y.1 = D.JDP n ε' →
      can6P (permRep (rhoEn n) (Δ6 M)) D.i x y =
        canAtP M (planeFaceRepr j') hM (faceRep M (planeFaceRepr j') n) ⟨ε, hε⟩ ⟨toLitP (M := M) n (planeFaceRepr j') ε', hε'⟩

/-- **Planes.**  For classes `ε` (coefficients `E_n`) and `ε'` (coefficients `E_n^∨`, as in `PDmod`) of the plane group of `j'` which are mixed (`ε'` after `toLitP`) and whose Mackey
transports are mixed (forward mixedness for planes is not proved), the level-6 canonical pairing of the transports equals the level-`M` canonical pairing. -/
def PlaneCanIdent (M n : ℕ) [NeZero M] (hM : 3 ≤ M) (h6 : 6 ∣ M) : Prop :=
  ∀ j' : PlaneFaces M, PlaneCanIdentAt n hM (planeOverOf h6 j')

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
