module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1Trivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreTarget

@[expose] public section


/-!
# Local nondegeneracy at the good line `L₁` for the trivial character, unconditionally

The Hecke adjointness of the level-one parabolic cup pairing of `Sym^{n+1}` with
`Sym^{n+1} ⊗ det⁻¹` (`AdjCore.parabolicPairingHeckeAdjoint_trivial`) is the only input left in
`LocalPairingCaseL1Trivial.localNondegenerate_L1_trivial`; discharging it gives local nondegeneracy at
the good line for the trivial character in every degree `n ≥ 3`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1TrivialFinal

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.CuspFullness (LocalNondegenerate)
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2 (good)

variable {n : ℕ}

/-- **Local nondegeneracy at the good line `L₁` for the trivial character** (`3 ≤ n`, nonzero pair),
with no hypothesis. -/
theorem localNondegenerate_L1_trivial_unconditional (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 1 (good 1) :=
  LocalPairingCaseL1Trivial.localNondegenerate_L1_trivial hn D hχ hecke hhecke hne
    (fun hodd => AdjCore.parabolicPairingHeckeAdjoint_trivial hodd)

/-- **The good-line trivial-character input of `LocalPairingL2`**, unconditionally. -/
theorem goodLineTrivialInput_unconditional (hn : 3 ≤ n) :
    LocalPairingL2.GoodLineTrivialInput n :=
  LocalPairingCaseL1Trivial.goodLineTrivialInput hn
    (fun hodd => AdjCore.parabolicPairingHeckeAdjoint_trivial hodd)

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1TrivialFinal

end
