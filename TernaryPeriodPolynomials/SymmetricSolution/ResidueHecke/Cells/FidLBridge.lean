module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.T0Coeff
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Lemma33Geometric

@[expose] public section


/-!
# Lemma B.1: `FidL` against the coefficient at `T₀`, unconditionally

Formalized by Claude Sonnet 5.5.

`FidL_eq_coeff`: with A2's unconditional apartment bridge (`Statements.Lemma33Geometric.apartment_evaluation_eq_coefficient`),
there is one nonzero rational `c` such that `FidL w = c · lit₀ comp₀ (coeffAtT0 z)` for every cell cycle `z` of
`cellCoinv (Res_{Γ(6)} 𝓡_n)` representing `ι_* w`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence CategoryTheory
open TernaryPoly.OrdinaryResidueSupport (axis)
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.Lemma33.Retract

theorem FidL_eq_coeff : ∃ c : ℚ, c ≠ 0 ∧ ∀ (n : ℕ) (w : groupHomology (Rep.res PN.subtype (FibRep n)) 3)
    (z : (cellCoinv (Rep.res principalSix.subtype (ResRep n))).X 3)
    (hz : ((cellCoinv (Rep.res principalSix.subtype (ResRep n))).d 3 2).hom z = 0),
    (cellGroupHomologyMap (Rep.res principalSix.subtype (ResRep n)) 3).hom
      (cellClass (Rep.res principalSix.subtype (ResRep n)) z hz) = iotaStar n w →
    FidL n w = c • literalFiberMap n 0 (component n (axis 0)
      ((coeffAtT0 (Rep.res principalSix.subtype (ResRep n))).hom z)) := by
  obtain ⟨c, hc, h⟩ := TernaryPeriodPolynomials.Argument.Statements.Lemma33Geometric.apartment_evaluation_eq_coefficient
  refine ⟨c, hc, fun n w z hz hzw => ?_⟩
  change literalFiberMap n 0 (component n (axis 0)
      ((OrdinaryTopBoundaryComparison.groupApartmentEvaluation
        (Rep.res principalSix.subtype (ResRep n))).hom (iotaStar n w))) = _
  rw [← hzw, h]
  simp only [map_smul]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
