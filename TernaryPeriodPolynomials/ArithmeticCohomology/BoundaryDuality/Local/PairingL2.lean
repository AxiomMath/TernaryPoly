module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ParityCases
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.Reduction

@[expose] public section


/-!
# Boundary duality on the associate pair from the four local cases

Boundary duality on the associate pair reduces to local nondegeneracy of the boundary pairing at
the line cusps (`CoordinateInputs.associatePairDuality_of_localNondegenerate`); by the parity
analysis (`ParityCases`) the nonvacuous cases are
* the good line `L₁` in odd degree, for the trivial character and for a nontrivial character of
  conductor dividing three (`GoodLineTrivialInput`, `GoodLineNontrivialInput`), and
* the bad line `L₀` for the trivial character, in even and in odd degree
  (`ParityCases.BadLineEvenInput`, `ParityCases.BadLineOddInput`).
Given these, boundary duality holds for every inducing datum of degree at least three, for the
canonical Hecke operators of the maximal strata (`associatePairDuality_of_cases`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingL2

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace
open TernaryPeriodPolynomials.BoundaryDuality.CuspFullness
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2
open TernaryPeriodPolynomials.BoundaryDuality.ParityCases

variable {n : ℕ}

/-- **Good line, odd degree, trivial character**: local nondegeneracy at `L₁`. -/
def GoodLineTrivialInput (n : ℕ) : Prop :=
  ∀ (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke), D.chi = trivialCharacter → Odd n →
    associatePair D ≠ ⊥ →
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 1 (good 1)

/-- **Good line, odd degree, nontrivial character** (of conductor dividing three, since the pair
is nonzero): local nondegeneracy at `L₁`. -/
def GoodLineNontrivialInput (n : ℕ) : Prop :=
  ∀ (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke), D.chi ≠ trivialCharacter → Odd n →
    associatePair D ≠ ⊥ →
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 1 (good 1)

/-- The good-line input in odd degree from its trivial and nontrivial cases. -/
theorem goodLineOddInput_of_cases (h₁ : GoodLineTrivialInput n) (h₂ : GoodLineNontrivialInput n) :
    GoodLineOddInput n := by
  intro D hecke hhecke hodd hne
  by_cases hχ : D.chi = trivialCharacter
  · exact h₁ D hecke hhecke hχ hodd hne
  · exact h₂ D hecke hhecke hχ hodd hne

/-- **Boundary duality on the associate pair from the four local cases**, for any Hecke data. -/
theorem associatePairDuality_of_cases_hecke (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (goodTrivial : GoodLineTrivialInput n) (goodNontrivial : GoodLineNontrivialInput n)
    (badEven : BadLineEvenInput n) (badOdd : BadLineOddInput n) : AssociatePairDuality D :=
  associatePairDuality_of_parityInputs hn D hecke hhecke
    (goodLineOddInput_of_cases goodTrivial goodNontrivial) badEven badOdd

/-- **Boundary duality on the associate pair from the four local cases**, with the canonical Hecke
operators of the maximal strata. -/
theorem associatePairDuality_of_cases (hn : 3 ≤ n) (D : InducingData n)
    (goodTrivial : GoodLineTrivialInput n) (goodNontrivial : GoodLineNontrivialInput n)
    (badEven : BadLineEvenInput n) (badOdd : BadLineOddInput n) : AssociatePairDuality D :=
  associatePairDuality_of_cases_hecke hn D (GraphPieces.Reduction.canonicalStratumHecke n D.chi)
    (GraphPieces.Reduction.canonicalStratumHecke_realizes n D.chi) goodTrivial goodNontrivial
    badEven badOdd

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingL2
