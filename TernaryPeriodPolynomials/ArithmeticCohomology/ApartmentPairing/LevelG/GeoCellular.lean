module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Fixed
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Geometric.GeoMain

@[expose] public section


open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.OrdinaryApartmentPresentation
  TernaryPoly.OrdinaryBoundaryCone
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.Lemma33.Normalized (coeffAtGen)
open TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport (d5)
open TernaryPeriodPolynomials.Argument.Lemma33.Geometric (PDboundaryGeo groupApartmentEvaluationGeo)
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary)

/-!
# Level G in geometric orientations

Formalized by Claude Sonnet 5.5.

Corollary of `Geometric.groupApartmentEvaluationGeo_apply`/`geoEval_cell` and
`levelG_diagram`: at level `G` the geometric evaluator of the (`d₅`-rescaled) cellular top cycle is `-coeff_{T₀}` (constant `-1`,
only the sign of `T₀` free); `levelG_cellular_geo`.  Replaces the library-normalized `levelG_cellular` (`coeffAtT0Norm`, a scale
artefact) as the statement matching the paper's orientation convention.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

variable (n : ℕ) (e : ℤ)

/-- The geometric boundary Poincaré duality of the rescaled level-`G` class `d₅ • res ω` is the restriction of `ω`. -/
theorem PDboundaryGeo_resToBoundary (ω : (fullBoundaryCochains n e).homology 1) :
    PDboundaryGeo (restrictedCoefficients n e) (d5 • resToBoundary n e ω) =
      homologyMap (restrBd n e) 1 ω := by
  have h := Geometric.PDboundaryGeo_apply (restrictedCoefficients n e) (d5 • resToBoundary n e ω)
  rw [h]
  change d5⁻¹ • (PDboundary (restrictedCoefficients n e)).hom (d5 • resToBoundary n e ω) = _
  rw [map_smul, smul_smul, inv_mul_cancel₀ Normalized.d5_ne_zero', one_smul]
  exact PDboundary_resToBoundary n e ω

/-- **Lemma 3.3 at level `G` in geometric orientations** (the geometric counterpart of `levelG_cellular`): for every
`ω ∈ H¹(∂X̄_G; M)` the geometric class `j_*(PD^{geo}_∂)⁻¹ res ω = d₅ • j_*(PD_∂)⁻¹ res ω` is the class of a cellular top cycle `z`
of the neat-level cell complex, and `F_{j^G_* ω}(ℓ) = ⟨ω, ∂a⟩` equals `-coeff_{T₀}(z)` with NO rescaling of `T₀`; only the sign
of `T₀` is a free orientation choice (reversing it, `coeffAtGen (-1)`, reads the coefficient literally).  The flat and its boundary,
the coordinate apartment (hence the bottom arrow), are untouched. -/
theorem levelG_cellular_geo (ω : (fullBoundaryCochains n e).homology 1) :
    ∃ (z : (cellCoinv (restrictedCoefficients n e)).X 3)
      (hz : ((cellCoinv (restrictedCoefficients n e)).d 3 2).hom z = 0),
      d5 • fullBoundaryClassToGroup n e ω =
          cellGroupHomologyMap (restrictedCoefficients n e) 3 (cellClass (restrictedCoefficients n e) z hz) ∧
        fullBoundaryPairing n e ω = (coeffAtGen (-1) (restrictedCoefficients n e)).hom z ∧
        topEvaluationG (actualCoefficients n e) (fullBoundaryClassToG n e ω) =
          (coeffAtGen (-1) (restrictedCoefficients n e)).hom z := by
  obtain ⟨y, hy⟩ := cellGroupHomologyMap_surjective (restrictedCoefficients n e)
    (d5 • fullBoundaryClassToGroup n e ω)
  obtain ⟨z, hz, rfl⟩ := exists_cellClass (restrictedCoefficients n e) y
  have h1 : groupApartmentEvaluation (restrictedCoefficients n e) (fullBoundaryClassToGroup n e ω) =
      (coeffAtGen (-1) (restrictedCoefficients n e)).hom z := by
    have h2 := Geometric.geoEval_cell (restrictedCoefficients n e) z hz
    rw [hy, Geometric.groupApartmentEvaluationGeo_apply, map_smul, smul_smul, inv_mul_cancel₀
      Normalized.d5_ne_zero', one_smul] at h2
    rw [h2, Normalized.coeffAtGen_apply, inv_neg, inv_one]
  refine ⟨z, hz, hy.symm, ?_, ?_⟩
  · rw [← levelG_diagram, topEvaluationG_fullClass, h1]
  · rw [topEvaluationG_fullClass, h1]

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
