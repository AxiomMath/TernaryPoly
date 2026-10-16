module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerRadical
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineLocal
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction

@[expose] public section


/-!
# Nonvanishing of the bad-line edge class of an `InnerBoundary` line class (M1, bad line)

The bad-line analogue of `GoodLineEdgeNonvanishing.lean`'s nonvanishing step, but simpler: no
transport (`psiL`) is needed, because the bad-line cusp residue `cuspRes n trivialCharacter .line
false` *is already* the direct restriction to `standardBadLine` (`cuspFlag .line false =
standardBadLine` by `rfl`, both being `QuotientGroup.mk (1 : RationalGL3)`), with no intervening
`Γ`-translate.

**Membership.** `innerBoundary_fixedPointH2_locallyInner` (`LocalInner.lean`, fully generic over
any flag) places that restriction directly in `locallyInnerClasses n trivialCharacter .line
standardBadLine`. `locallyInner_standardBadLine_radical_zero` (`InnerRadical.lean`) turns *bare*
`locallyInnerClasses`-membership (no `VanishesOnGood` needed) directly into
`badLineLocalRadicalKernel n`-membership, i.e. exactly `badLineEdge`'s domain
(`BadLineLocal.lean`/`BadLineFinal.lean`): this single pre-existing lemma already does the
reconciliation that `KLMembership.lean` has to assemble by hand on the good-line side, so no
analogue of that file is needed here.

**Nonvanishing.** `badLineEdge_injective` (`BadLineFinal.lean`) then turns nonvanishing of that
cusp residue directly into nonvanishing of its `badLineEdge` image: a single injective linear map,
no composition needed (unlike the good line's `psiL_injective ∘ edgeK_injective`).

This is *only* the nonvanishing half of bad-line M1: parabolicity (membership in
`parabolicCrossedH1 (binaryArithmeticRepresentation n)`) is a materially stronger, all-cusps
condition (`binaryParabolicH1`'s defining infimum ranges over every `GL(2,Q)`-frame,
`InnerParabolic.lean`) that bare `InnerBoundary` does not supply; that direction still needs
`VanishesOnGood` and Sol's `innerBadLineClasses`/`innerBadLineArithmeticBinaryMap_parabolic` route and is not addressed here.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
open TernaryPeriodPolynomials.LevelThree.BadLineFinal

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M1, bad line, membership step.** The bad-line cusp residue of an `InnerBoundary` line class
lies in `badLineLocalRadicalKernel`, i.e. in the domain of `badLineEdge`. -/
theorem cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary {n : ℕ}
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate) :
    cuspRes n trivialCharacter .line false coordinate ∈ badLineLocalRadicalKernel n :=
  locallyInner_standardBadLine_radical_zero n _
    (innerBoundary_fixedPointH2_locallyInner inner standardBadLine)

/-- **M1, bad line, nonvanishing step.** If an `InnerBoundary` line coordinate's bad-line cusp
residue is nonzero, its bad-line edge class is nonzero. -/
theorem badLineEdge_ne_zero_of_cuspRes_ne_zero {n : ℕ} (hn : 0 < n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate)
    (hcusp : cuspRes n trivialCharacter .line false coordinate ≠ 0) :
    badLineEdge n hn ⟨cuspRes n trivialCharacter .line false coordinate,
        cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary inner⟩ ≠ 0 := by
  intro h
  apply hcusp
  exact Subtype.ext_iff.mp (badLineEdge_injective n hn (h.trans (map_zero (badLineEdge n hn)).symm))

end TernaryPeriodPolynomials.Argument.FacePairing
