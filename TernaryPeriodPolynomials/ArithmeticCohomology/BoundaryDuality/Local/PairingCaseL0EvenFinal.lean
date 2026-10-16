module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Target

@[expose] public section


/-!
# The bad line, trivial character, even degree: the case input without hypotheses

`LocalPairingCaseL0EvenMain.badLineEvenInput_of_plain` reduces `ParityCases.BadLineEvenInput n` to
the plain Hecke adjointness `PlainEvenHeckeAdjoint` of the cup pairing of
`H¹_par(Γ₁'(3), Sym^{n+1})` with itself, which `AdjL3.evenPairing_hecke_adjoint` proves.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

/-- **Local nondegeneracy at the bad line for the trivial character and even degree** (the
`BadLineEvenInput` of `ParityCases`), unconditionally. -/
theorem badLineEvenInput_unconditional {n : ℕ} (hn : 3 ≤ n) : ParityCases.BadLineEvenInput n :=
  badLineEvenInput_of_plain hn fun heven p hp3 => AdjL3.evenPairing_hecke_adjoint heven p hp3

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

end
