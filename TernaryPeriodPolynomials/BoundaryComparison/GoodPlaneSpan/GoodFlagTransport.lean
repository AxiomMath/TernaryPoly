module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspOrbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.AutomorphicSpan

@[expose] public section


/-!
# Single-reference-flag vanishing implies `VanishesOnGood`

This closes a gap in the argument: `VanishesOnGood` quantifies
over *every* good flag of a side, but all that the rest of the argument naturally produces is
vanishing of the Shapiro coordinate at the single *reference* good flag `cuspFlag side true`. The
bridge is generic and mechanical, independent of side and degree: every good flag is a
`rationalLevel`-translate of the reference one (`cuspFlag_transporter`, from the good-flag orbit
theorems in `CuspOrbits.lean`), and `fixedPointH2` at a translate is the *linear* image, under
`stabilizerTransportH2`, of `fixedPointH2` at the source (`stabilizerTransportH2_fixedPointH2`).
Since a linear map sends `0` to `0`, vanishing transports from the one reference flag to every
good flag at once.

This is *not* specific to the good plane: it applies verbatim to any `side : Side`. It was not
packaged as a standalone lemma anywhere in the library (the only existing
`VanishesOnGood`-constructing usages are `AutomorphicSpan.lean`'s `mem_innerBadLineClasses_iff`,
which merely unpacks an *already*-universal hypothesis via `Submodule.mem_iInf`, and the trivial
zero-class case in `GoodFlags.lean`).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits

/-- **Single reference flag suffices.** If the Shapiro coordinate of `a` at the single reference good flag
vanishes, then `a` vanishes at *every* good flag, i.e. `VanishesOnGood`. Generic in `side`. -/
theorem vanishesOnGood_of_cuspRes_good_eq_zero {n : ℕ} {χ : RankOneCharacter} {side : Side}
    (a : StratumH2 n χ side) (h : cuspRes n χ side true a = 0) :
    VanishesOnGood n χ side a := by
  refine (vanishesOnGood_iff_fixedPointH2 a).mpr ?_
  intro flag hflag
  obtain ⟨γ, hγ⟩ := cuspFlag_transporter side true flag ⟨fun _ => rfl, fun _ => hflag⟩
  have key := stabilizerTransportH2_fixedPointH2 rationalLevel
    (rationalCoefficientComponent n χ) γ (cuspFlag side true) flag hγ a
  have hzero : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
      (cuspFlag side true) a = 0 := h
  rw [hzero, map_zero] at key
  exact key.symm

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
