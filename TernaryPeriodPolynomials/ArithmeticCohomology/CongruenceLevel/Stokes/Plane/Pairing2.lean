module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Pairing1
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Pairing2

@[expose] public section


/-!
# The plane pairing from the Mackey transports

Formalized by Claude Sonnet 5.5.

For a plane face `j'` of `Γ(M)` over `(j, O)`, `JEP`, `JDP` transport classes of the plane group of `j'` (coefficients `E_n`, resp. `E_n^∨`) to the `e_O`-components of the line (plane) group classes of `Γ(6)`; `betaP`
is the bilinear form `can6P(JEP ε, JDP ε')` on the (sub)spaces where both arguments are mixed, extended to all classes by choosing left inverses of the inclusions of those subspaces.
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

section PlanePair

variable {M : ℕ} [NeZero M] (n : ℕ) {j' : PlaneFaces M} (D : PlaneOver M j')

/-- `toLiteral` for the plane group, with target typed as the cohomology of `dualRepG (faceRep M h n)`. -/
def toLitP (h : SL(3, ℤ)) : groupCohomology.H2 (Rep.of ((dualRhoC M n).comp (Subgroup.inclusion (gammaNPAt_le M h)))) →ₗ[ℂ]
    groupCohomology.H2 (dualRepG (faceRep M h n)) :=
  toLiteral (gammaNPAt M h) (gammaNPAt_le M h) n

/-- The `E`-side plane transport `H²(Γ_{P'}, E_n) → H²(K_j, Res V)`. -/
def PlaneOver.JEP : groupCohomology.H2 (faceRep M (planeFaceRepr j') n) →ₗ[ℂ]
    groupCohomology.H2 (Rep.res (planeIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)))) :=
  (toKP D.i (Rep.of (permRep (rhoEn n) (Δ6 M)))).comp (D.thetaGen (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))

/-- The dual-side plane transport `H²(Γ_{P'}, E_n^∨) → H²(K_j, Res V^*)`. -/
def PlaneOver.JDP : groupCohomology.H2 (Rep.of ((dualRhoC M n).comp (Subgroup.inclusion (gammaNPAt_le M (planeFaceRepr j'))))) →ₗ[ℂ]
    groupCohomology.H2 (Rep.res (planeIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)) :=
  (toKP D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)).comp
    ((dualPushG (rhoEn n) (Δ6 M) (planeSub D.i)).comp
      ((D.thetaGen (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))).comp
        (toLitP (M := M) n (planeFaceRepr j'))))

/-- The subspace of classes whose `E`-side transport is mixed. -/
def PlaneOver.UE : Submodule ℂ (groupCohomology.H2 (faceRep M (planeFaceRepr j') n)) :=
  Submodule.comap (D.JEP n) (planeMixedSub (permRep (rhoEn n) (Δ6 M)) D.i)

/-- The subspace of dual classes whose transport is mixed. -/
def PlaneOver.UD : Submodule ℂ (groupCohomology.H2 (Rep.of ((dualRhoC M n).comp (Subgroup.inclusion (gammaNPAt_le M (planeFaceRepr j')))))) :=
  Submodule.comap (D.JDP n) (planeMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i)

end PlanePair

section Beta

variable {M : ℕ} [NeZero M] (n : ℕ) {j' : PlaneFaces M} (D : PlaneOver M j')

/-- The bilinear form `can6P` on the mixed classes of the plane face `i` of `Γ(6)`. -/
def can6PBil {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6) :
    planeMixedSub ρ i →ₗ[ℂ] planeMixedSub ρ.dual i →ₗ[ℂ] ℂ :=
  (facePairingCan (by norm_num : 3 ≤ 6) (faceSplitting 6 (planeFaceRepr i)) (planeFaceRadicalInput_det 6 (planeFaceRepr i))
    (planeRepAt ρ i)).compl₁₂ (planeMixedToCusp ρ i) (planeMixedToCuspDual ρ i)

theorem can6PBil_apply {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6) (x : planeMixedSub ρ i) (y : planeMixedSub ρ.dual i) :
    can6PBil ρ i x y = can6P ρ i x y := rfl

/-- `JEP` restricted to the classes with mixed image. -/
def PlaneOver.JEPm : D.UE n →ₗ[ℂ] planeMixedSub (permRep (rhoEn n) (Δ6 M)) D.i :=
  ((D.JEP n).domRestrict (D.UE n)).codRestrict _ (fun u => u.2)

/-- `JDP` restricted to the classes with mixed image. -/
def PlaneOver.JDPm : D.UD n →ₗ[ℂ] planeMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i :=
  ((D.JDP n).domRestrict (D.UD n)).codRestrict _ (fun u => u.2)

/-- The bilinear form on the mixed subspaces. -/
def PlaneOver.beta0 : D.UE n →ₗ[ℂ] D.UD n →ₗ[ℂ] ℂ :=
  (can6PBil (permRep (rhoEn n) (Δ6 M)) D.i).compl₁₂ (D.JEPm n) (D.JDPm n)

omit [NeZero M] in
theorem PlaneOver.exists_retraction_E : ∃ r : groupCohomology.H2 (faceRep M (planeFaceRepr j') n) →ₗ[ℂ] D.UE n,
    r.comp (D.UE n).subtype = LinearMap.id :=
  LinearMap.exists_leftInverse_of_injective (D.UE n).subtype (by simp)

theorem PlaneOver.exists_retraction_D : ∃ r : groupCohomology.H2 (Rep.of ((dualRhoC M n).comp (Subgroup.inclusion (gammaNPAt_le M (planeFaceRepr j'))))) →ₗ[ℂ] D.UD n,
    r.comp (D.UD n).subtype = LinearMap.id :=
  LinearMap.exists_leftInverse_of_injective (D.UD n).subtype (by simp)

/-- **The plane form on all classes**: `can6P(J ε, J' ε')` on the subspaces where both transports are mixed, extended through chosen retractions. -/
def PlaneOver.betaP : groupCohomology.H2 (faceRep M (planeFaceRepr j') n) →ₗ[ℂ]
    groupCohomology.H2 (Rep.of ((dualRhoC M n).comp (Subgroup.inclusion (gammaNPAt_le M (planeFaceRepr j'))))) →ₗ[ℂ] ℂ :=
  (D.beta0 n).compl₁₂ (Classical.choose (D.exists_retraction_E n)) (Classical.choose (D.exists_retraction_D n))

theorem PlaneOver.betaP_apply (ε : groupCohomology.H2 (faceRep M (planeFaceRepr j') n)) (hε : ε ∈ D.UE n)
    (ε' : groupCohomology.H2 (Rep.of ((dualRhoC M n).comp (Subgroup.inclusion (gammaNPAt_le M (planeFaceRepr j')))))) (hε' : ε' ∈ D.UD n) :
    D.betaP n ε ε' = can6P (permRep (rhoEn n) (Δ6 M)) D.i ⟨D.JEP n ε, hε⟩ ⟨D.JDP n ε', hε'⟩ := by
  have h1 := LinearMap.congr_fun (Classical.choose_spec (D.exists_retraction_E n)) ⟨ε, hε⟩
  have h2 := LinearMap.congr_fun (Classical.choose_spec (D.exists_retraction_D n)) ⟨ε', hε'⟩
  have e1 : Classical.choose (D.exists_retraction_E n) ε = ⟨ε, hε⟩ := h1
  have e2 : Classical.choose (D.exists_retraction_D n) ε' = ⟨ε', hε'⟩ := h2
  change D.beta0 n (Classical.choose (D.exists_retraction_E n) ε) (Classical.choose (D.exists_retraction_D n) ε') = _
  rw [e1, e2]
  rfl

end Beta

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
