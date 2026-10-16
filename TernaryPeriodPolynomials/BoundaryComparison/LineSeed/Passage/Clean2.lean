module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Bridge5
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineConj

@[expose] public section


/-!
# The coordinate side of the frame change (Passage frame, part P1)

`h2Map_faceToStd_frame`: for `b ∈ lineBorel` and a transporter `q`, the transport map along `faceToStd` at the frame `b * h'` is the frame transport (`frameHomQ`, with the identity coefficient comparison `frameT`)
of the transport map at `h'`.  `phiLineAt_clean'`: hence, if `h'` is a clean frame for `q` (`mapGL ℚ h' * q = Π`), the Shapiro coordinate formula at the frame `b * h'` is the frame transport of the
clean-frame formula at `h'`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix CategoryTheory groupCohomology
open TernaryPeriodPolynomials.Argument.LevelTransfer

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.LineCoordinates (Λ₁)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.KDaggerComparison (stdLine faceToStd stdRep faceToStd_hT)

section

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (n : ℕ) (h' b : SL(3, ℤ)) (hb : b ∈ lineBorel) {q : RationalGL3}
  (hq : q ∈ rationalLevel) (hF : q • stdLine = lineFlagAt (b * h')) (hF' : q • stdLine = lineFlagAt h')

omit [NeZero N] in
theorem faceToStd_frame (p : ↥(gammaNQAt N (b * h'))) :
    faceToStd N h3 (b * h') hq hF p = faceToStd N h3 h' hq hF' (frameHomQ N h' b hb p) := by
  apply Subtype.ext
  rw [KDaggerComparison.faceToStd_val, KDaggerComparison.faceToStd_val, coe_frameHomQ]

omit [NeZero N] in
theorem h2Map_comp_gen {G H K : Type} [Group G] [Group H] [Group K] (α : H →* G) (β : K →* H) (γ : K →* G)
    (hγ : ∀ k, γ k = α (β k)) (A : Rep ℂ G) (B : Rep ℂ H) (C : Rep ℂ K) (T₁ : A →ₗ[ℂ] B) (T₂ : B →ₗ[ℂ] C)
    (T₃ : A →ₗ[ℂ] C) (hcomp : ∀ v, T₃ v = T₂ (T₁ v))
    (hT₁ : ∀ (g : H) (v : A), T₁ (A.ρ (α g) v) = B.ρ g (T₁ v))
    (hT₂ : ∀ (g : K) (v : B), T₂ (B.ρ (β g) v) = C.ρ g (T₂ v))
    (hT₃ : ∀ (g : K) (v : A), T₃ (A.ρ (γ g) v) = C.ρ g (T₃ v)) (Y : groupCohomology.H2 A) :
    EdgeNat.h2Map γ A C T₃ hT₃ Y = EdgeNat.h2Map β B C T₂ hT₂ (EdgeNat.h2Map α A B T₁ hT₁ Y) := by
  induction Y using groupCohomology.H2_induction_on with | _ z => ?_
  have e1 := EdgeNat.h2Map_π γ A C T₃ hT₃ z
  have e2 := EdgeNat.h2Map_π α A B T₁ hT₁ z
  have e3 := EdgeNat.h2Map_π β B C T₂ hT₂ (mapCocycles₂ α (EdgeNat.comparison α A B T₁ hT₁) z)
  refine e1.trans (Eq.trans ?_ ((congrArg (EdgeNat.h2Map β B C T₂ hT₂) e2).trans e3).symm)
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, c⟩ := p
  refine (mapCocycles₂_apply_edgeNat γ A C T₃ hT₃ z a c).trans (Eq.trans ?_
    ((mapCocycles₂_apply_edgeNat β B C T₂ hT₂ _ a c).trans
      (congrArg T₂ (mapCocycles₂_apply_edgeNat α A B T₁ hT₁ z (β a) (β c)))).symm)
  rw [hcomp, hγ, hγ]

omit [NeZero N] in
theorem h2Map_faceToStd_frame (Y : groupCohomology.H2 (stdRep N n)) :
    EdgeNat.h2Map (faceToStd N h3 (b * h') hq hF) (stdRep N n) (lineFaceRep N (b * h') n)
        (rationalCoefficientComponent n trivialCharacter q) (faceToStd_hT N n h3 (b * h') hq hF) Y =
      EdgeNat.h2Map (frameHomQ N h' b hb) (lineFaceRep N h' n) (lineFaceRep N (b * h') n) (frameT n)
        (frameTQ_intertwines N h' n b hb)
        (EdgeNat.h2Map (faceToStd N h3 h' hq hF') (stdRep N n) (lineFaceRep N h' n)
          (rationalCoefficientComponent n trivialCharacter q) (faceToStd_hT N n h3 h' hq hF') Y) :=
  h2Map_comp_gen (faceToStd N h3 h' hq hF') (frameHomQ N h' b hb) (faceToStd N h3 (b * h') hq hF)
    (fun k => faceToStd_frame N h3 h' b hb hq hF hF' k) _ _ _ _ _ _ (fun _ => rfl) _ _ _ Y

end

end TernaryPeriodPolynomials.Argument.LineSeed
