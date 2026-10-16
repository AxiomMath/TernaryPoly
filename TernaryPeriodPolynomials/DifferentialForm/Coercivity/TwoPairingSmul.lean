module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeStar

@[expose] public section



/-! Helper for ISOMETRY: `twoPairing` is linear in its first argument with respect to a global
real scalar, i.e. `twoPairing (c • x) y = c * twoPairing x y`. Needed to turn
`twoPairing (star3to2_star2to3_self`'s `(1/96) • a`-shaped output back into a bare scalar factor
on `twoPairing a y`. Immediate from `factorialPairing`'s own bundled linearity in its first
argument. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem twoPairing_smul_left (c : ℝ) (x y : TwoCoordinates) :
    twoPairing (c • x) y = c * twoPairing x y := by
  simp [twoPairing, Pi.smul_apply, map_smul, Finset.mul_sum, mul_assoc, mul_left_comm]

end TernaryPeriodPolynomials.Argument.Coercivity
