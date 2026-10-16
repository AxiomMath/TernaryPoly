module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StandardBadLineMixedCuspidal
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspOrbits

@[expose] public section


/-!
# `InnerBoundary` is determined at the two reference cusps of a side

A maximal-stratum class has zero restriction to every complete flag (`InnerBoundary`) if and only
if its Shapiro coordinate at each of the two reference cusps of the side is locally inner, i.e.
restricts to zero on the stabilizer of every complete flag over the reference cusp
(`innerBoundary_iff_locallyInner_cusps`). On the line side the bad reference cusp is
`standardBadLine`, where locally inner is the paper's mixed cuspidal condition
(`innerBoundary_line_iff_mixedCuspidal`, end of Appendix C.4).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- **`InnerBoundary` is a condition at the two reference cusps.** -/
theorem innerBoundary_iff_locallyInner_cusps {n : ℕ} {χ : RankOneCharacter} {side : Side}
    (b : StratumH2 n χ side) :
    InnerBoundary n χ side b ↔
      ∀ v : Bool, fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
        (cuspFlag side v) b ∈ locallyInnerClasses n χ side (cuspFlag side v) := by
  constructor
  · intro inner v
    exact innerBoundary_fixedPointH2_locallyInner inner (cuspFlag side v)
  · intro h
    apply (innerBoundary_iff_locallyInner b).mpr
    intro flag
    by_cases hg : GoodFlag side flag
    · obtain ⟨γ, hγ⟩ := cuspFlag_transporter side true flag ⟨fun _ => rfl, fun _ => hg⟩
      rw [← stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
        γ (cuspFlag side true) flag hγ b]
      exact stabilizerTransportH2_locallyInner n χ side γ _ _ hγ _ (h true)
    · obtain ⟨γ, hγ⟩ := cuspFlag_transporter side false flag
        ⟨fun hh => absurd hh hg, fun hh => by simp at hh⟩
      rw [← stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
        γ (cuspFlag side false) flag hγ b]
      exact stabilizerTransportH2_locallyInner n χ side γ _ _ hγ _ (h false)

/-- **`InnerBoundary` ⇔ mixed cuspidal (line side).** A line class is `InnerBoundary` exactly when
its coordinate at the good reference line is locally inner and its coordinate at the bad reference
line `standardBadLine` has zero restriction to the radical and a mixed class vanishing at every
rational cusp of the binary Levi. -/
theorem innerBoundary_line_iff_mixedCuspidal (degree : ℕ)
    (b : StratumH2 degree trivialCharacter .line) :
    InnerBoundary degree trivialCharacter .line b ↔
      (fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
          (cuspFlag .line true) b ∈
        locallyInnerClasses degree trivialCharacter .line (cuspFlag .line true)) ∧
      MixedCuspidal degree
        (fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
          standardBadLine b) := by
  rw [innerBoundary_iff_locallyInner_cusps]
  constructor
  · intro h
    exact ⟨h true, MixedCuspidal.of_locallyInner degree _ (h false)⟩
  · rintro ⟨hgood, hbad⟩ v
    cases v
    · exact locallyInner_of_mixedCuspidal degree _ hbad
    · exact hgood

end TernaryPeriodPolynomials.Argument.FacePairingFull
