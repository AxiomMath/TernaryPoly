module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Geometric.GeoMain

@[expose] public section


/-!
# Lemma 3.3 (`lem:apartment-boundary-pairing`) with geometric orientations: the constant is `-1`, only `T₀`'s sign is free

Formalized by Claude Sonnet 5.5.

See
`Proofs/Lemma33/Geometric/GeoMain.lean`; this is the bundled statement.
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.Lemma33
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.Lemma33.Normalized
open TernaryPeriodPolynomials.Argument.Lemma33.Geometric
open TernaryPoly.OrdinaryTopBoundaryComparison
open TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport (d5)
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (flatBoundaryPairing)

namespace TernaryPeriodPolynomials.Argument.Statements.Lemma33GeoNormalized

/-- **Lemma 3.3 with geometric orientations.**

* the flat is the library's flat; its boundary is the coordinate apartment;
* the geometric fundamental class, boundary cap, Poincaré duality and top evaluator differ from the library's by the single
  rational factor `d₅` (resp. `d₅⁻¹`), where `d₅` is the degree of the positive staircase cell;
* the diagram commutes, and on cellular top cycles the geometric evaluator is `-1` times the coefficient at `T₀`;
* the reversed generator `-T₀` is the unique rescaling `r • T₀` with local intersection number `+1`. -/
theorem lemma_3_3_geometric :
    OrdinaryTopBoundaryComparison.upstairsRelativeSequence_shortExact.δ 2 1 rfl flatClass =
        identityApartmentBoundaryClass ∧
      (∀ W : Rep.{0} ℚ principalSix, ∀ x,
        groupApartmentEvaluationGeo W x = d5⁻¹ • groupApartmentEvaluation W x) ∧
      (∀ W : Rep.{0} ℚ principalSix, ∀ c,
        PDboundaryGeo W c = d5⁻¹ • Statements.Lemma33Diagram.PDboundary W c) ∧
      (∀ W : Rep.{0} ℚ principalSix,
        SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 ≫ groupApartmentEvaluationGeo W =
          PDboundaryGeo W ≫ flatBoundaryPairing W) ∧
      (∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
        groupApartmentEvaluationGeo W ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) =
          (-1 : ℚ) • (coeffAtT0 W).hom z) ∧
      (∀ r : ℚ, ReadsCoefficientGeo r 1 ↔ r = -1) ∧
      (∀ r : ℚ, geoLocalIntersection r = 1 ↔ r = -1) ∧
      (∀ (W : Rep.{0} ℚ principalSix) (c : (SingularLocalHomology.boundaryLocalChains W).homology 3)
        (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
        SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c = cellGroupHomologyMap W 3 (cellClass W z hz) →
          flatBoundaryPairing W (PDboundaryGeo W c) = (coeffAtGen (-1) W).hom z) :=
  ⟨delta_flatClass, groupApartmentEvaluationGeo_apply, PDboundaryGeo_apply, geoDiagram_commutes,
    geoEval_cell, readsCoefficientGeo_one_iff, geoLocalIntersection_eq_one_iff,
    fun W c z hz h => geoDiagram_literal_reversed W c z hz h⟩

end TernaryPeriodPolynomials.Argument.Statements.Lemma33GeoNormalized
