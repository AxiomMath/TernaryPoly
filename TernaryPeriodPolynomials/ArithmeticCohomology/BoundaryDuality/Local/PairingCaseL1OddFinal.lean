module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.LocalPairingCaseL1Odd
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingL2

@[expose] public section


/-!
# The good-line input for a nontrivial character

`LocalPairingL2.GoodLineNontrivialInput n`: local nondegeneracy at the good line `L₁` for a
nontrivial character with a nonzero associate pair, from the Hecke adjointness of the parabolic cup
pairing for the twists `(-1, 0)` (`LocalPairingCaseL1Odd.AdjointnessInput`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1OddFinal

variable {n : ℕ}

/-- **The good-line input for a nontrivial character** from the Hecke adjointness of the parabolic
cup pairing of `GL₂(ℤ)` on `Sym^{n+1} ⊗ det⁻¹ × Sym^{n+1}`. -/
theorem goodLineNontrivialInput (hn : 3 ≤ n)
    (hadj : ∀ hodd : Odd n, LocalPairingCaseL1Odd.AdjointnessInput n hodd) :
    LocalPairingL2.GoodLineNontrivialInput n :=
  fun D hecke hhecke hχ _ hne =>
    LocalPairingCaseL1Odd.localNondegenerate_L1_odd hn D hχ hecke hhecke hne hadj

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1OddFinal

end
