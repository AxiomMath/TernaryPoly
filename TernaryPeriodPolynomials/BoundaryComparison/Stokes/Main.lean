module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cone.Assembly
public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Uniform
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.Factorisation6Thm
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineInvariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.PlaneInvariance

@[expose] public section


/-!
# The literal Stokes lemma at `Γ(M)`, `6 ∣ M`, with the canonical face pairings

Formalized by Claude Sonnet 5.5.  Paper: Lemma `ar:lem:stokes`.

`stokes_literal_level`: for global classes `a ∈ H²(Γ(M), E_n)`, `b ∈ H²(Γ(M), E_n^*)` with zero flag restrictions (their face restrictions are then mixed, `lineMixedAt_of_zeroFlags`), the oriented sum of the canonical face pairings vanishes:
`ε_P ∑_{plane faces} ⟨r_P a, r_P b⟩_P + ε_Q ∑_{line faces} ⟨r_Q a, r_Q b⟩_Q = 0` with `canAtClassP`, `canAtClass` the canonical pairings (cup form of the modular curve times the Koszul pairing of the radical, `facePairingCan`) at the representative frames of the faces.
The orientation signs are those of the cone differential `d(α, β, u) = (dα, dβ, α|_{F_B} - β|_{F_B} - du)`: plane `+1`, line `-1` (`planeFaceOrientationSign`, `lineFaceOrientationSign`).

Inputs (named, not assumed silently): `FaceFactorisation6U` (the cone pairings of `Γ(6)` are the canonical ones up to the uniform constant `c`, lines `c`, planes `-c`: the `faceFactorisation6U_of_M3At`),
`Step1` (frame invariance, `frameInvarianceLine`/`frameInvariancePlane`, PROVED in `Proofs/FrameInvariance`), `Step2` (`OrbitIdentLine/Plane`: the Mackey/finite-index identification of the orbit components).
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
open MulAction

/-- The orientation sign of the plane faces in the cone differential `d(α, β, u) = (dα, dβ, α|_{F_B} - β|_{F_B} - du)`: the plane component enters with `+`. -/
def planeFaceOrientationSign : ℤ := 1

/-- The orientation sign of the line faces in the cone differential: the line component enters with `-`. -/
def lineFaceOrientationSign : ℤ := -1

section Literal

variable {M n : ℕ} [NeZero M]

/-- **The literal Stokes lemma at `Γ(M)`, `6 ∣ M`**, with the canonical face pairings and the face orientation signs. -/
theorem stokes_literal_level_of (h6 : 6 ∣ M) (hM : 3 ≤ M) (FF : FaceFactorisation6U) (S1 : Step1 M n hM) (S2 : Step2 M n hM)
    (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀) (c₀' : groupCohomology.H2 (gammaNRepAllDual M n))
    (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c₀') :
    (planeFaceOrientationSign : ℂ) * ∑ j : PlaneFaces M, canAtClassP M (planeFaceRepr j) n hM c₀ hz c₀' hz' +
      (lineFaceOrientationSign : ℂ) * ∑ i : LineFaces M, canAtClass M i.rep n hM c₀ hz c₀' hz' = 0 := by
  obtain ⟨c, hc, hF⟩ := FF
  obtain ⟨cV, hcV⟩ := (PhiH_bijective (rhoEn n) (Δ6 M)).2
    (transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
  obtain ⟨cVd, hcVd⟩ := (PhiH_bijective (rhoEn n).dual (Δ6 M)).2
    (transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) c₀')
  have hL := lineSum_eq h6 hM (fun _ => c) (fun i x y => (hF _ (permRep (rhoEn n) (Δ6 M))).1 i x y) S1.1 S2.1 c₀ hz c₀' hz'
    cV cVd hcV hcVd
  have hP := planeSum_eq h6 hM (fun _ => -c) (fun i x y => (hF _ (permRep (rhoEn n) (Δ6 M))).2 i x y) S1.2 S2.2 c₀ hz c₀' hz'
    cV cVd hcV hcVd
  have h0 := gamma6_stokes_ind_M M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀ c₀' (fun g => hz g) (fun g => hz' g)
    cV hcV cVd hcVd
  have hstokes : stokesSum (rhoEn n) (Δ6 M) cV (h2Hom (dualRepHom (rhoEn n) (Δ6 M)) cVd) =
      (∑ i : LineFaces 6, ∑ o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M),
        lineFacePairM (permRep (rhoEn n) (Δ6 M)) i (lineTermX c₀ hz cV hcV i o).1 (lineTermY c₀' hz' cVd hcVd i o).1) +
      (∑ i : PlaneFaces 6, ∑ o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M),
        planeFacePairM (permRep (rhoEn n) (Δ6 M)) i (planeTermX c₀ hz cV hcV i o).1 (planeTermY c₀' hz' cVd hcVd i o).1) := rfl
  rw [hstokes, hL, hP] at h0
  simp only [planeFaceOrientationSign, lineFaceOrientationSign, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul]
  have h1 : (∑ i' : LineFaces M, c * canAtClass M i'.rep n hM c₀ hz c₀' hz') =
      c * ∑ i' : LineFaces M, canAtClass M i'.rep n hM c₀ hz c₀' hz' := (Finset.mul_sum _ _ _).symm
  have h2 : (∑ j' : PlaneFaces M, -c * canAtClassP M (planeFaceRepr j') n hM c₀ hz c₀' hz') =
      -c * ∑ j' : PlaneFaces M, canAtClassP M (planeFaceRepr j') n hM c₀ hz c₀' hz' := (Finset.mul_sum _ _ _).symm
  rw [h1, h2] at h0
  have h3 : c * (∑ j : PlaneFaces M, canAtClassP M (planeFaceRepr j) n hM c₀ hz c₀' hz' -
      ∑ i : LineFaces M, canAtClass M i.rep n hM c₀ hz c₀' hz') = 0 := by linear_combination -h0
  have h4 := (mul_eq_zero.1 h3).resolve_left hc
  linear_combination h4

/-- **The literal Stokes lemma at `Γ(M)`, `6 ∣ M`, with every input proved except Step 2** (`OrbitIdentLine/Plane`, S4/S7): the uniform factorisation `faceFactorisation6U` (S2) and the frame invariance of
the canonical pairing (`frameInvarianceLine`, `frameInvariancePlane`, S5) are theorems. -/
theorem stokes_literal_level (h6 : 6 ∣ M) (hM : 3 ≤ M) (S2 : Step2 M n hM)
    (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀) (c₀' : groupCohomology.H2 (gammaNRepAllDual M n))
    (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c₀') :
    (planeFaceOrientationSign : ℂ) * ∑ j : PlaneFaces M, canAtClassP M (planeFaceRepr j) n hM c₀ hz c₀' hz' +
      (lineFaceOrientationSign : ℂ) * ∑ i : LineFaces M, canAtClass M i.rep n hM c₀ hz c₀' hz' = 0 :=
  stokes_literal_level_of h6 hM GammaNFaceFactor.faceFactorisation6U
    ⟨FrameInvariance.frameInvarianceLine M n hM, FrameInvariance.frameInvariancePlane M n hM⟩ S2 c₀ hz c₀' hz'

/-- **The literal Lemma `ar:lem:stokes` at `Γ(N)`**, as a Prop: for every pair of global classes `a ∈ H²(Γ(N), E_n)`, `b ∈ H²(Γ(N), E_n^*)` with zero flag restrictions (so that their face restrictions are mixed cuspidal),
the oriented sum of the canonical face pairings (`canAtClassP`, `canAtClass`: cup form of the modular curve times the Koszul pairing of the radical, at the representative frames of the faces) vanishes. -/
def StokesGammaNLiteral (N n : ℕ) [NeZero N] (hN : 3 ≤ N) : Prop :=
  ∀ (c₀ : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c₀) (c₀' : groupCohomology.H2 (gammaNRepAllDual N n))
    (hz' : ZeroFlagsRep (gammaNRepAll N n).ρ.dual c₀'),
    (planeFaceOrientationSign : ℂ) * ∑ j : PlaneFaces N, canAtClassP N (planeFaceRepr j) n hN c₀ hz c₀' hz' +
      (lineFaceOrientationSign : ℂ) * ∑ i : LineFaces N, canAtClass N i.rep n hN c₀ hz c₀' hz' = 0

/-- The literal Stokes lemma for `Γ(M)`, `6 ∣ M`, from Step 2. -/
theorem stokesGammaNLiteral_of_six_dvd (h6 : 6 ∣ M) (hM : 3 ≤ M) (S2 : Step2 M n hM) : StokesGammaNLiteral M n hM :=
  fun c₀ hz c₀' hz' => stokes_literal_level h6 hM S2 c₀ hz c₀' hz'

end Literal

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
