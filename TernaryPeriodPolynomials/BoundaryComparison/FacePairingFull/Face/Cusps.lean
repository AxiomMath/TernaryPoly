module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.GoodPlane
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.GoodLine
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.BadPlane
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.InnerBoundaryCusps

@[expose] public section


/-!
# `InnerBoundary` in Hochschild-Serre form at the four named reference cusps

`InnerBoundary` is a condition at one good and one bad flag of the side, and the choice of flag in
an orbit is immaterial (`innerBoundary_iff_locallyInner_reps`). Combined with the Hochschild-Serre
descriptions of local innerness at the four stabilizers (`badLine_`, `goodLine_`, `badPlane_`,
`goodPlane_locallyInner_iff`), this gives `innerBoundary_line_iff_hs` and
`innerBoundary_plane_iff_hs`: a maximal stratum class is `InnerBoundary` exactly when, at each of
its two named reference flags, the coordinate has zero restriction to the face radical and a mixed
class vanishing on the binary stabilizer of every complete flag over the reference flag.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (goodLineSplitting identityPlaneSplitting)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

/-- Local innerness of the Shapiro coordinate is invariant along a level translate of the flag. -/
theorem locallyInner_fixedPoint_iff_of_orbit {n : ℕ} {χ : RankOneCharacter} {side : Side}
    (F₁ F₂ : Flags side) (γ : rationalLevel) (hγ : γ.val • F₁ = F₂) (b : StratumH2 n χ side) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) F₁ b ∈
        locallyInnerClasses n χ side F₁ ↔
      fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) F₂ b ∈
        locallyInnerClasses n χ side F₂ := by
  have hγ' : (γ⁻¹).val • F₂ = F₁ := by
    rw [← hγ]
    change γ.val⁻¹ • γ.val • F₁ = F₁
    exact inv_smul_smul _ _
  constructor
  · intro h
    rw [← stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
      γ F₁ F₂ hγ b]
    exact stabilizerTransportH2_locallyInner n χ side γ _ _ hγ _ h
  · intro h
    rw [← stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
      γ⁻¹ F₂ F₁ hγ' b]
    exact stabilizerTransportH2_locallyInner n χ side γ⁻¹ _ _ hγ' _ h

/-- **`InnerBoundary` at arbitrary representatives of the good and bad orbits.** -/
theorem innerBoundary_iff_locallyInner_reps {n : ℕ} {χ : RankOneCharacter} {side : Side}
    (Fgood Fbad : Flags side) (hgood : GoodFlag side Fgood) (hbad : ¬ GoodFlag side Fbad)
    (b : StratumH2 n χ side) :
    InnerBoundary n χ side b ↔
      (fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) Fgood b ∈
        locallyInnerClasses n χ side Fgood) ∧
      (fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) Fbad b ∈
        locallyInnerClasses n χ side Fbad) := by
  rw [innerBoundary_iff_locallyInner_cusps]
  obtain ⟨γ₁, hγ₁⟩ := cuspFlag_transporter side true Fgood ⟨fun _ => rfl, fun _ => hgood⟩
  obtain ⟨γ₀, hγ₀⟩ := cuspFlag_transporter side false Fbad
    ⟨fun hh => absurd hh hbad, fun hh => by simp at hh⟩
  rw [← locallyInner_fixedPoint_iff_of_orbit _ _ γ₁ hγ₁,
    ← locallyInner_fixedPoint_iff_of_orbit _ _ γ₀ hγ₀]
  constructor
  · intro h
    exact ⟨h true, h false⟩
  · rintro ⟨h1, h0⟩ v
    cases v
    · exact h0
    · exact h1

theorem goodPlaneFlag_good : GoodFlag .plane goodPlaneFlag := by
  refine ⟨![0, 0, 1], ⟨dualInvolution 1 * longWeyl, rfl, ![1, 0, 0], rfl, ?_⟩, by decide⟩
  funext i
  fin_cases i <;>
    simp [map_one, longWeyl, longWeylMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem goodLineFlag_good : GoodFlag .line goodLineFlag :=
  TernaryPeriodPolynomials.SphericalDetection.Helpers.rationalGoodLine_good

theorem standardBadLine_not_good : ¬ GoodFlag .line standardBadLine :=
  line_identity_not_good

theorem badPlaneFlag_not_good : ¬ GoodFlag .plane badPlaneFlag :=
  plane_identity_not_good

section HS

variable {Radical Levi : Type} [Group Radical] [Group Levi] (action : Levi →* MulAut Radical)
  (degree : ℕ) (character : RankOneCharacter) {side : Side} (F : Flags side)
  (ι : SemidirectProduct Radical Levi action ≃* fixedPointLevel rationalLevel F)

/-- **The Hochschild-Serre (mixed cuspidal) condition at a flag.** The coordinate has zero
restriction to the radical, and its mixed class vanishes after pullback to the binary stabilizer of
every complete flag over `F`. -/
def HSInner (coordinate : H2 (fixedPointLevel rationalLevel F)
    (rationalCoefficientComponent degree character)) : Prop :=
  ∃ radicalZero : faceH2Equiv action degree character F ι coordinate ∈
      (radicalRestrictionH2 action (faceRep action degree character F ι)).ker,
    ∀ e : Edges, endpoint side e = F →
      crossedPullbackH1 (faceCusp action F ι e).subtype
        (leviCrossedH1Representation action (faceRep action degree character F ι))
        (radicalKernelMixedMap action (faceRep action degree character F ι)
          ⟨faceH2Equiv action degree character F ι coordinate, radicalZero⟩) = 0

end HS

/-- **`InnerBoundary` on the line side in Hochschild-Serre form.** A line class is
`InnerBoundary` exactly when its coordinate at the good line `⟨(3,0,1)ᵀ-type reference⟩`
(`goodLineFlag`) and at the standard bad line both satisfy the mixed cuspidal condition. -/
theorem innerBoundary_line_iff_hs (degree : ℕ) (b : StratumH2 degree trivialCharacter .line) :
    InnerBoundary degree trivialCharacter .line b ↔
      HSInner goodLineSplitting.conjAct degree trivialCharacter goodLineFlag
          goodLineSemidirectEquivFixed
          (fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
            goodLineFlag b) ∧
      HSInner integralBadLineSplitting.conjAct degree trivialCharacter standardBadLine
          standardBadLineSemidirectEquiv
          (fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
            standardBadLine b) := by
  rw [innerBoundary_iff_locallyInner_reps goodLineFlag standardBadLine goodLineFlag_good
    standardBadLine_not_good]
  exact and_congr (goodLine_locallyInner_iff degree trivialCharacter _)
    (badLine_locallyInner_iff degree trivialCharacter _)

/-- **`InnerBoundary` on the plane side in Hochschild-Serre form.** A plane class is
`InnerBoundary` exactly when its coordinate at the good plane (`goodPlaneFlag`, the dual of the
standard bad line) and at the identity plane both satisfy the mixed cuspidal condition. -/
theorem innerBoundary_plane_iff_hs (degree : ℕ) (b : StratumH2 degree trivialCharacter .plane) :
    InnerBoundary degree trivialCharacter .plane b ↔
      HSInner integralBadLineSplitting.conjAct degree trivialCharacter goodPlaneFlag
          goodPlaneSemidirectEquiv
          (fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
            goodPlaneFlag b) ∧
      HSInner identityPlaneSplitting.conjAct degree trivialCharacter badPlaneFlag
          badPlaneSemidirectEquiv
          (fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
            badPlaneFlag b) := by
  rw [innerBoundary_iff_locallyInner_reps goodPlaneFlag badPlaneFlag goodPlaneFlag_good
    badPlaneFlag_not_good]
  exact and_congr (goodPlane_locallyInner_iff degree trivialCharacter _)
    (badPlane_locallyInner_iff degree trivialCharacter _)

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
