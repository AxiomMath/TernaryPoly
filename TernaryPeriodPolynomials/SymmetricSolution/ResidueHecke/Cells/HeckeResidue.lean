module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HomModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BinaryHeckePeriods

@[expose] public section


/-!
# Lemma B.1: the prime Hecke operator in the literal residue coordinate

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.3
("The Hecke transfer") and `eq:Hecke-formula`.

In the Hom model the prime Hecke correspondence of `diag(1,1,p)` on `Hom_G(St, R_n ⊗ det⁻¹)` is
the library's `OrdinaryHomHecke.rationalHecke`; transported along the literal residue coordinate
`res_H` it equals `p • T₂(p) + 1`, where `T₂(p)` is the binary prime correspondence on
`BinaryModularSymbol` Homs transported to the period coordinate.  This is the library's
`OrdinaryBinaryHecke.period_prime` restated for `res_H`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly

theorem resH_eq_periodEquiv (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1)) :
    resH n F = OrdinaryResiduePeriod.periodEquiv n F := rfl

/-- **Hecke compatibility in the residue coordinate.** -/
theorem resH_hecke_prime (n p : ℕ) [Fact p.Prime]
    (F : OrdinaryFullCoefficient.ResidueHom n (-1)) :
    resH n (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
        (SinglePole.residueAction n (-1)) F) =
      (p : ℚ) • BinaryRationalHecke.periodHecke (n + 1)
        (BinaryRationalHeckePrime.primeDiagonal p) (resH n F) + resH n F := by
  have h := OrdinaryBinaryHecke.period_prime n p (OrdinaryResiduePeriod.periodEquiv n F)
  rw [OrdinaryResiduePeriod.periodHecke_equiv] at h
  exact h

end TernaryPeriodPolynomials.Argument.AppendixBResidue
