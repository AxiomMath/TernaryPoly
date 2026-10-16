module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1OddFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreTarget

@[expose] public section


/-!
# The good-line input for a nontrivial character, with the adjointness discharged

`LocalPairingCaseL1OddFinal.goodLineNontrivialInput` takes the Hecke adjointness of the parabolic cup
pairing for the twists `(-1, 0)` as a hypothesis. It is supplied by
`AdjCore.parabolicPairingHeckeAdjoint_odd`, which gives the unconditional input.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1OddUnconditional

variable {n : ℕ}

/-- **The good-line input for a nontrivial character**, unconditionally in terms of the level-one
Hecke adjointness of `AdjCore`. -/
theorem goodLineNontrivialInput_unconditional (hn : 3 ≤ n) :
    LocalPairingL2.GoodLineNontrivialInput n :=
  LocalPairingCaseL1OddFinal.goodLineNontrivialInput hn fun hodd =>
    AdjCore.parabolicPairingHeckeAdjoint_odd hodd

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1OddUnconditional

end
