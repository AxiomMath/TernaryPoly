module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddThetaHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Target

@[expose] public section


/-!
# The bad-line case of odd degree, unconditionally

`ParityCases.BadLineOddInput n` (local nondegeneracy of the boundary trace at the bad line `L₀` for
the trivial character and odd `n`, for every nonzero associate pair) for `3 ≤ n`: the standard
level-three adjointness `AdjointLevelThreePairing.BadGoodHeckeAdjoint` of the Lefschetz pairing is
`AdjL3.badGoodHeckeAdjoint`, and `LocalPairingCaseL0OddThetaHecke.badLineOddInput_of_standardAdjoint`
derives the bad-line case from it (the comparison `localJointGen ≤ localJoint` at the good plane is
`HeckeGenEq.localJointGen_eq_localJoint_goodPlane_trivial`, and the commutation of the transport
with the Hecke operators `T_p` is `thetaHeckeCommute`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd

/-- **The bad-line case of odd degree, unconditionally** (`3 ≤ n`):
`ParityCases.BadLineOddInput n`. -/
theorem badLineOddInput_unconditional {n : ℕ} (hn : 3 ≤ n) : ParityCases.BadLineOddInput n :=
  badLineOddInput_of_standardAdjoint hn fun hodd => AdjL3.badGoodHeckeAdjoint hodd

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd

end
