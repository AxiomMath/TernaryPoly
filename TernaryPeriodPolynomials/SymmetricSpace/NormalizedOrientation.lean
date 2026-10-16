module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Lemma33GeoNormalized
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.OrientationSentence

@[expose] public section


/-!
# Lemma 3.3 with the paper-normalized pair (flat, averaged top-cell generator)

Formalized by Claude Sonnet 5.5.

Paper: "We orient the flat and the averaged standard top-cell
generator so that their local intersection number is `+1`.  With this normalization, the next lemma compares evaluation of a boundary class
with its boundary intersection pairing."

The orientation of the flat and of the generator is a CHOICE.  The library's fixed generator `T₀` has local intersection number `-1`
with the flat whose boundary is the coordinate apartment (`Geometric.geoLocalIntersection_eq`); this is a convention of the library, not a
statement of the paper.  Here the chosen pair is constructed and the sign is propagated through the statements of Lemma 3.3.  No definition is changed; everything is added next to them.

* `avgGenT0 = [T₀]` is the averaged standard top-cell generator: the orientation-character-weighted average of the translates of `[T₀]`
  over a set of elements fixing the standard cell is `[T₀]` (`Naturality.avgGenT0_eq`).
* `avgGenPaper = -avgGenT0` is the paper-normalized generator (`flat` orientation untouched, boundary = coordinate apartment).
* **"Local intersection number" is realized as the normal-projection degree at the transverse point**: the flat `{unip = 0}` meets the
  standard cell at the identity matrix, the chain `r • T₀` is projected along the unipotent coordinates to `ℝ³`
  (`Retract.LocalDegree.degπ`, i.e. the class of `π_* c` in `H₃(ℝ³, ℝ³ ∖ 0) ≅ ℚ`), the degree `Normalized.localDegreeGen r = degπ (r • T₀)`
  is compared with the positive orientation of the normal space (`Geometric.geoLocalDegree r = localDegreeGen r / lamPos`), and multiplied by
  the geometric cross constant `1` (`Geometric.geo_cross_constant`, transversality and the product orientation of the 5-dimensional space):
  `Geometric.geoLocalIntersection r` (value `-r`).  `paperLocalIntersection v` below is this number for the generator `v` (its scale at `T₀`).
* `coeffPaper W` is the coefficient of a cellular top chain against the paper generator, `-coeff_{T₀}`.
* `apartment_evaluation_eq_coefficient_paper`: in geometric orientations and for the paper pair the top evaluator reads the coefficient
  LITERALLY, with constant `1` (compare the existential `apartment_evaluation_eq_coefficient` with an unspecified nonzero `c`).
* `lemma_3_3_paper_normalized`: the bundled statement.
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence Finsupp
open TernaryPeriodPolynomials.Argument.Lemma33
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPeriodPolynomials.Argument.Lemma33.Normalized
open TernaryPeriodPolynomials.Argument.Lemma33.Geometric
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (flatBoundaryPairing)
open TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport (d5)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Identities.Orientation

open scoped Classical

/-- The averaged standard top-cell generator `[T₀]` (the generator of the oriented cell resolution at the standard cell). -/
def avgGenT0 : Graded 3 →₀ ℚ := single T0g (1 : ℚ)

/-- **The paper-normalized averaged top-cell generator**: the standard generator with the opposite orientation, `-[T₀]`. -/
def avgGenPaper : Graded 3 →₀ ℚ := -avgGenT0

theorem avgGenPaper_eq_single : avgGenPaper = single T0g (-1 : ℚ) := by
  unfold avgGenPaper avgGenT0
  rw [Finsupp.single_neg]

/-- The scale of an oriented generator at the standard cell: `v = r • [T₀]` has scale `r`. -/
def generatorScale (v : Graded 3 →₀ ℚ) : ℚ := v T0g

theorem generatorScale_smul (r : ℚ) : generatorScale (r • avgGenT0) = r := by
  simp [generatorScale, avgGenT0]

theorem generatorScale_avgGenT0 : generatorScale avgGenT0 = 1 := by
  simp [generatorScale, avgGenT0]

theorem generatorScale_avgGenPaper : generatorScale avgGenPaper = -1 := by
  simp [generatorScale, avgGenPaper, avgGenT0]

/-- **The local intersection number of the flat with the oriented generator `v`**, realized as the normal-projection degree at the
transverse point (the identity matrix): `Geometric.geoLocalIntersection (generatorScale v)`, which unfolds to
`(pairingConstant · lamPos / d₅) · (degπ (r • T₀) / lamPos)` with `r = generatorScale v`. -/
def paperLocalIntersection (v : Graded 3 →₀ ℚ) : ℚ := geoLocalIntersection (generatorScale v)

/-- The normal-projection degree (`degπ`, positive normal orientation) of the paper generator is `+1`. -/
theorem normalDegree_avgGenPaper : geoLocalDegree (generatorScale avgGenPaper) = 1 := by
  rw [generatorScale_avgGenPaper, geoLocalDegree_eq]; norm_num

/-- The standard generator has normal-projection degree `-1`. -/
theorem normalDegree_avgGenT0 : geoLocalDegree (generatorScale avgGenT0) = -1 := by
  rw [generatorScale_avgGenT0, geoLocalDegree_eq]

/-- **With the paper-normalized generator the local intersection number is `+1`.** -/
theorem paperLocalIntersection_avgGenPaper : paperLocalIntersection avgGenPaper = 1 := by
  unfold paperLocalIntersection
  rw [geoLocalIntersection_eq, generatorScale_avgGenPaper]; norm_num

/-- The library's standard generator has local intersection number `-1` (the library convention). -/
theorem paperLocalIntersection_avgGenT0 : paperLocalIntersection avgGenT0 = -1 := by
  unfold paperLocalIntersection
  rw [geoLocalIntersection_eq, generatorScale_avgGenT0]

/-- The paper-normalized generator is the unique multiple of `[T₀]` with local intersection number `+1`. -/
theorem paperLocalIntersection_smul_eq_one_iff (r : ℚ) :
    paperLocalIntersection (r • avgGenT0) = 1 ↔ r • avgGenT0 = avgGenPaper := by
  unfold paperLocalIntersection
  rw [generatorScale_smul, geoLocalIntersection_eq_one_iff]
  constructor
  · rintro rfl
    unfold avgGenPaper
    rw [neg_one_smul]
  · intro h
    have := congrArg generatorScale h
    rwa [generatorScale_smul, generatorScale_avgGenPaper] at this

/-- **The paper generator is again an averaged generator**: the orientation-character-weighted average of its translates over any
finite set of elements fixing the standard cell is itself. -/
theorem avgGenPaper_average (S : Finset GeneralEisenstein.IntegralGL3) (hS : S.Nonempty)
    (hfix : ∀ g ∈ S, glGraded 3 g T0g = T0g) :
    (S.card : ℚ)⁻¹ • ∑ g ∈ S, cellSign g T0g.1.val • twistLin 3 g avgGenPaper = avgGenPaper := by
  unfold avgGenPaper avgGenT0
  simp only [map_neg, smul_neg, Finset.sum_neg_distrib]
  rw [Naturality.avgGenT0_eq S hS hfix]

/-- The coefficient of a cellular top chain against the paper generator: `-coeff_{T₀}`. -/
def coeffPaper (W : Rep.{0} ℚ principalSix) : (cellCoinv W).X 3 ⟶ ModuleCat.of ℚ W :=
  coeffAtGen (generatorScale avgGenPaper) W

theorem coeffPaper_apply (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) :
    (coeffPaper W).hom z = -(coeffAtT0 W).hom z := by
  unfold coeffPaper
  rw [coeffAtGen_apply, generatorScale_avgGenPaper, inv_neg, inv_one, neg_smul, one_smul]

/-- **Lemma 3.3 (coefficient dictionary), paper normalization.**  In geometric orientations and for the paper pair, the top evaluator
`z ↦ φ(F_z)` of a cellular top cycle `z` is its coefficient against the paper generator: the constant is `1`, not an unspecified
nonzero `c` as in `Statements.Lemma33Geometric.apartment_evaluation_eq_coefficient`. -/
theorem apartment_evaluation_eq_coefficient_paper (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
    (hz : ((cellCoinv W).d 3 2).hom z = 0) :
    groupApartmentEvaluationGeo W ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) = (coeffPaper W).hom z := by
  rw [geoEval_cell, coeffPaper_apply, neg_one_smul]

theorem readsCoefficientGeo_paper : ReadsCoefficientGeo (generatorScale avgGenPaper) 1 :=
  (readsCoefficientGeo_one_iff _).2 generatorScale_avgGenPaper

/-- **The equivalent normalization by the oppositely oriented flat**: with the flat `-a` (boundary `-∂a`) and the library's generator
`[T₀]`, the local intersection number is also `+1` and the geometric top evaluator reads `+coeff_{T₀}`. -/
theorem apartment_evaluation_oppositeFlat (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
    (hz : ((cellCoinv W).d 3 2).hom z = 0) :
    d5⁻¹ • groupFlatEvaluation ((-1 : ℚ) • flatClass) W ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) =
      (coeffAtT0 W).hom z := by
  rw [groupFlatEvaluation_smul, groupFlatEvaluation_flatClass, smul_comm, ← groupApartmentEvaluationGeo_apply,
    geoEval_cell]
  simp

theorem orientedIntersection_oppositeFlat :
    Naturality.orientedIntersection (-1) (generatorScale avgGenT0) = 1 := by
  unfold Naturality.orientedIntersection
  rw [geoLocalIntersection_eq, generatorScale_avgGenT0]; norm_num

theorem orientedIntersection_paperPair :
    Naturality.orientedIntersection 1 (generatorScale avgGenPaper) = 1 := by
  unfold Naturality.orientedIntersection
  rw [geoLocalIntersection_eq, generatorScale_avgGenPaper]; norm_num

/-- **Lemma 3.3 (`lem:apartment-boundary-pairing`) with the paper-normalized pair, literally.**

The flat is the library's flat (its boundary is the coordinate apartment); the averaged generator is `avgGenPaper = -[T₀]`.

1. `δ [flat] =` the coordinate apartment class;
2. the local intersection number (normal-projection degree at the identity) of the flat with the paper generator is `+1`, and the paper
   generator is the unique multiple of `[T₀]` with this property; the library's `[T₀]` has `-1`;
3. the paper generator is an averaged generator (its weighted stabilizer average is itself);
4. the top evaluator `z ↦ φ(F_z)` of every cellular top cycle is its coefficient against the paper generator, with constant `1`;
5. the diagram commutes (boundary Poincaré duality, geometric orientation);
6. in the diagram, if `j_* c` is the class of the cellular top cycle `z`, then `⟨PD_∂ c, ∂a⟩ =` the coefficient of `z` against the paper
   generator, literally. -/
theorem lemma_3_3_paper_normalized :
    OrdinaryTopBoundaryComparison.upstairsRelativeSequence_shortExact.δ 2 1 rfl flatClass =
        OrdinaryTopBoundaryComparison.identityApartmentBoundaryClass ∧
      (paperLocalIntersection avgGenPaper = 1 ∧ paperLocalIntersection avgGenT0 = -1 ∧
        ∀ r : ℚ, paperLocalIntersection (r • avgGenT0) = 1 ↔ r • avgGenT0 = avgGenPaper) ∧
      (∀ (S : Finset GeneralEisenstein.IntegralGL3), S.Nonempty → (∀ g ∈ S, glGraded 3 g T0g = T0g) →
        (S.card : ℚ)⁻¹ • ∑ g ∈ S, cellSign g T0g.1.val • twistLin 3 g avgGenPaper = avgGenPaper) ∧
      (∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
        groupApartmentEvaluationGeo W ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) = (coeffPaper W).hom z) ∧
      (∀ W : Rep.{0} ℚ principalSix,
        SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 ≫ groupApartmentEvaluationGeo W =
          PDboundaryGeo W ≫ flatBoundaryPairing W) ∧
      (∀ (W : Rep.{0} ℚ principalSix) (c : (SingularLocalHomology.boundaryLocalChains W).homology 3)
        (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
        SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c = cellGroupHomologyMap W 3 (cellClass W z hz) →
          flatBoundaryPairing W (PDboundaryGeo W c) = (coeffPaper W).hom z) :=
  ⟨delta_flatClass, ⟨paperLocalIntersection_avgGenPaper, paperLocalIntersection_avgGenT0,
      paperLocalIntersection_smul_eq_one_iff⟩, fun S hS hf => avgGenPaper_average S hS hf,
    apartment_evaluation_eq_coefficient_paper, geoDiagram_commutes,
    fun W c z hz h => by
      rw [geoDiagram_literal W c z hz h, coeffPaper_apply, neg_one_smul]⟩


/-- **The paper's orientation sentence for the chosen pair.**  "We orient the flat and the averaged standard top-cell generator so that their local intersection number is `+1`":
the flat is the library's flat (whose boundary is the coordinate apartment), the generator is the averaged `avgGenPaper`; their local intersection number (normal-projection degree at the transverse
point, `Geometric.geoLocalIntersection`) is `+1` (`Naturality.orientedIntersection 1 (-1) = 1`), and with this normalization the diagram of Lemma 3.3 reads the top-cell coefficient literally. -/
theorem paper_orientation_sentence_paper :
    Naturality.orientedIntersection 1 (generatorScale avgGenPaper) = 1 ∧
      OrdinaryTopBoundaryComparison.upstairsRelativeSequence_shortExact.δ 2 1 rfl flatClass =
        OrdinaryTopBoundaryComparison.identityApartmentBoundaryClass ∧
      (∀ (S : Finset GeneralEisenstein.IntegralGL3), S.Nonempty → (∀ g ∈ S, glGraded 3 g T0g = T0g) →
        (S.card : ℚ)⁻¹ • ∑ g ∈ S, cellSign g T0g.1.val • twistLin 3 g avgGenPaper = avgGenPaper) ∧
      (∀ (W : Rep.{0} ℚ principalSix) (c : (SingularLocalHomology.boundaryLocalChains W).homology 3)
        (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
        SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c = cellGroupHomologyMap W 3 (cellClass W z hz) →
          flatBoundaryPairing W (PDboundaryGeo W c) = (coeffPaper W).hom z) :=
  ⟨orientedIntersection_paperPair, delta_flatClass, fun S hS hf => avgGenPaper_average S hS hf,
    fun W c z hz h => by rw [geoDiagram_literal W c z hz h, coeffPaper_apply, neg_one_smul]⟩

end TernaryPeriodPolynomials.Argument.Identities.Orientation
