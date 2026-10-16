module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.TwoSideSelf
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.IsometryAdjoint
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.TwoPairingSmul

@[expose] public section



/-! ISOMETRY: `threePairing (star2to3 a) (star2to3 b) = (1/96) * twoPairing a b` for `a`
alternating. Assembled from three independently-checked pieces: the unconditional adjunction
`star3to2_star2to3_adjoint_iso` (`IsometryAdjoint.lean`), the two-sided involution
helper `star3to2_star2to3_self` (`StarTwoSideSelf.lean`), and the scalar-linearity helper
`twoPairing_smul_left` (`TwoPairingSmul.lean`). Only `a` needs to be alternating: the adjunction
and the scalar-linearity step are unconditional, and the involution collapse is the only step that
needs `a`'s alternation; `b` never passes through `star3to2 ∘ star2to3`, so no hypothesis on `b`
is needed for this statement to hold. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem hodgeStarRule_isometry (a b : TwoCoordinates) (ha : IsAlternatingTwo a) :
    threePairing (star2to3 a) (star2to3 b) = (1/96 : ℝ) * twoPairing a b := by
  rw [← star3to2_star2to3_adjoint_iso (star2to3 a) b, star3to2_star2to3_self a ha,
    twoPairing_smul_left]

end TernaryPeriodPolynomials.Argument.Coercivity
