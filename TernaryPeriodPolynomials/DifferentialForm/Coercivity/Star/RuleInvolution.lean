module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.ThreeSideSelf

@[expose] public section



/-! INVOLUTION: `star2to3 (star3to2 b) = (1/96) • b` for `b` alternating. This is the final
deliverable item for the three-sided Hodge-star involution; the entire proof content lives in
`star2to3_star3to2_self` (`StarThreeSideSelf.lean`, assembled from the five `StarThreeSideSelfAux
{0,1,2,3,4}.lean` first-index slices), and this file only restates it under the `hodgeStarRule_*`
naming convention shared with R1/R2/R3/R4/COMPOSITE/ISOMETRY. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem hodgeStarRule_involution (b : ThreeCoordinates) (hb : IsAlternatingThree b) :
    star2to3 (star3to2 b) = (1/96 : ℝ) • b :=
  star2to3_star3to2_self b hb

end TernaryPeriodPolynomials.Argument.Coercivity
