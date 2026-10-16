module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Geometric.GeoClasses
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Geometric.PosOrientation5
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.Calibration

@[expose] public section


/-!
# Lemma 3.3 in geometric orientations: only a sign reversal of the standard top cell

Formalized by Claude Sonnet 5.5.

With the geometric orientations of `PosOrientation5`/`GeoClasses`
(orientations fixed by positive reference cells, not by the library's choice-made rational generators) the top evaluator of a
cellular top cycle is `-1` times the coefficient at the standard top cell `T₀` (`geoEval_cell`), the diagram commutes with
the untouched flat and its boundary the coordinate apartment (`geoDiagram_commutes`, `geoDiagram_literal`), and the local
intersection of the flat with `r • T₀` is `+1` exactly for `r = -1` (`geoLocalIntersection_eq_one_iff`,
`readsCoefficientGeo_one_iff`): only the SIGN of `T₀` is a free orientation choice.  The number `-1` is computed from the
geometric local data: the standard cell has degree `-1` against the positive normal orientation (`geo_topCell_degree`), the
geometric cross-product constant is `1` (`geo_cross_constant`, the 5-dimensional orientation is the product of the positive
normal and flat orientations), the flat is positively oriented in the log-pivot plane (`geo_flat_positive`).
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.Lemma33
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.Lemma33.Normalized
open TernaryPoly.OrdinaryTopBoundaryComparison
open TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport (d5)
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Geometric

/-- **The diagram of Lemma 3.3 for the geometric orientation** commutes, with the library's bottom arrow (the flat and its
boundary, the coordinate apartment, are untouched). -/
theorem geoDiagram_commutes (W : Rep.{0} ℚ principalSix) :
    SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 ≫ groupApartmentEvaluationGeo W =
      PDboundaryGeo W ≫ flatBoundaryPairing W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change groupApartmentEvaluationGeo W (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c) =
    flatBoundaryPairing W (PDboundaryGeo W c)
  rw [groupApartmentEvaluationGeo_apply, PDboundaryGeo_apply, map_smul, Statements.Lemma33Diagram.diagram_apply]

/-- **The geometric top evaluator reads minus the top-cell coefficient**, for every cellular top cycle, with no rescaling of
`T₀`: `F_z(ℓ) = -coeff_{T₀}(z)`. -/
theorem geoEval_cell (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
    (hz : ((cellCoinv W).d 3 2).hom z = 0) :
    groupApartmentEvaluationGeo W ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) =
      (-1 : ℚ) • (coeffAtT0 W).hom z := by
  rw [groupApartmentEvaluationGeo_apply,
    Statements.Lemma33Geometric.apartment_evaluation_eq_neg_d5_coefficient W z hz, smul_smul]
  have := Normalized.d5_ne_zero'
  rw [show d5⁻¹ * -d5 = (-1 : ℚ) by field_simp]

/-- Reading with the geometric evaluator: the top evaluator is `n` times the coefficient against the generator `r • T₀`. -/
def ReadsCoefficientGeo (r n : ℚ) : Prop :=
  ∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
    groupApartmentEvaluationGeo W ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) =
      n • (coeffAtGen r W).hom z

theorem readsCoefficientGeo_iff_lib (r n : ℚ) : ReadsCoefficientGeo r n ↔ ReadsCoefficient r (d5 * n) := by
  have hd := Normalized.d5_ne_zero'
  constructor
  · intro h W z hz
    have e := h W z hz
    rw [groupApartmentEvaluationGeo_apply] at e
    have e2 := congrArg (fun v => d5 • v) e
    simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at e2
    rw [e2]
  · intro h W z hz
    rw [groupApartmentEvaluationGeo_apply, h W z hz, smul_smul, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

/-- **The geometric weights**: reading with weight `n` against `r • T₀` iff `-1 = n r⁻¹`. -/
theorem readsCoefficientGeo_iff (r n : ℚ) : ReadsCoefficientGeo r n ↔ -1 = n * r⁻¹ := by
  have hd := Normalized.d5_ne_zero'
  rw [readsCoefficientGeo_iff_lib, readsCoefficient_iff]
  constructor
  · intro h
    apply mul_left_cancel₀ hd
    rw [mul_neg_one, ← mul_assoc]
    exact h
  · intro h
    calc -d5 = d5 * (-1) := by ring
      _ = d5 * (n * r⁻¹) := by rw [h]
      _ = d5 * n * r⁻¹ := by ring

/-- **Only a sign reversal of `T₀` is needed**: the geometric top evaluator reads the coefficient against `r • T₀` with weight
`+1` exactly for `r = -1`. -/
theorem readsCoefficientGeo_one_iff (r : ℚ) : ReadsCoefficientGeo r 1 ↔ r = -1 := by
  rw [readsCoefficientGeo_iff, one_mul]
  constructor
  · intro h
    have hr : r ≠ 0 := by
      rintro rfl
      simp at h
    have := congrArg (fun t => r * t) h
    simp only [mul_neg, mul_one, mul_inv_cancel₀ hr] at this
    linarith
  · rintro rfl
    norm_num

/-! ### The geometric local numbers -/

open TernaryPoly.RationalRelativeSingular TernaryPoly.EuclideanLocalHomology

/-- **The standard top cell has degree `-1` against the positive geometric orientation of the normal space `ℝ³`**:
its projected class in `H₃(ℝ³, ℝ³∖0)` is minus the class of a positive tetrahedron (`tetra_generator_at`). -/
theorem geo_topCell_degree :
    (Orient.relCls (RationalSphere.Punctured 3)
        (Orient.AbF.map ((RationalSingularAugmentation.chainMap Retract.LocalDegree.piR3).f 3)
          (cellAtSpace 3 Retract.Cell0Geometry.T0))
        Retract.LocalDegree.cycle_T0 : (relativeChains (RationalSphere.Punctured 3)).homology 3) =
      (-1 : ℚ) • (Orient.posOrientation.generator 0 : (relativeChains (RationalSphere.Punctured 3)).homology 3) := by
  have h := Orient.topCell_class_eq_ratio Orient.posOrientation
  rw [Orient.ratio_pos] at h
  exact h

/-- The geometric cross-product constant, `κ · lamPos / d₅ = 1`.  This line is definitional (`pairingConstant := d₅ / lamPos`,
`Normalized/Main.lean`, proved by `field_simp`).  The geometric content it records is `pairingConstant_spec`: the constant `κ` of the
flat-intersection bridge equals `d₅ / lamPos`, which comes from the planar degree `+1` of the formal flat in the log-pivot chart
(`apartment_orientation_sign`, `OrientTransport.FlatValue.exists_universal_ratio_value`) and the product-chart pairing
`d₅ · ⟨ , ⟩ = lamPos · lam2` (`ChartOriented.chart_pair_oriented`): the positive 5-dimensional (staircase) orientation is the
product of the positive normal orientation (`lamPos`) and the positive flat orientation. -/
theorem geo_cross_constant : pairingConstant * Orient.lamPos / d5 = 1 := by
  have hl := Orient.lamPos_ne_zero
  have hd := Normalized.d5_ne_zero'
  unfold pairingConstant
  field_simp

/-- The geometric local degree of the generator `r • T₀` against the positive normal orientation. -/
def geoLocalDegree (r : ℚ) : ℚ := localDegreeGen r / Orient.lamPos

theorem geoLocalDegree_eq (r : ℚ) : geoLocalDegree r = -r := by
  have hl := Orient.lamPos_ne_zero
  unfold geoLocalDegree
  rw [localDegreeGen_eq, Orient.dT0_eq_neg_lamPos]
  field_simp

/-- **The geometric local intersection number of the flat with `r • T₀`**: the geometric cross constant (`1`, by
`geo_cross_constant`, i.e. by the proved facts that the flat is transverse with planar degree `+1` and the 5-dimensional orientation
is the product orientation) times the local degree of `r • T₀` against the positive normal orientation.  As a definition it is
`1 * (localDegreeGen r / lamPos)`; its value `-r` (`geoLocalIntersection_eq`) uses those facts. -/
def geoLocalIntersection (r : ℚ) : ℚ := (pairingConstant * Orient.lamPos / d5) * geoLocalDegree r

theorem geoLocalIntersection_eq (r : ℚ) : geoLocalIntersection r = -r := by
  unfold geoLocalIntersection
  rw [geo_cross_constant, geoLocalDegree_eq, one_mul]

/-- **Intersection with the flat reads the coefficient, in geometric orientations**: for `r ≠ 0` the weight is the geometric
local intersection number `-r`. -/
theorem readsCoefficientGeo_localIntersection {r : ℚ} (hr : r ≠ 0) :
    ReadsCoefficientGeo r (geoLocalIntersection r) := by
  rw [readsCoefficientGeo_iff, geoLocalIntersection_eq]
  field_simp

/-- The geometric local intersection number is `+1` exactly for the reversed generator. -/
theorem geoLocalIntersection_eq_one_iff (r : ℚ) : geoLocalIntersection r = 1 ↔ r = -1 := by
  rw [geoLocalIntersection_eq]
  constructor <;> intro h <;> linarith

/-- **The geometric orientation is the chart pull-back of the positive reference cell's orientation**: on the covering space
`Space` of positive forms, with the global Euclidean coordinates `spaceHomeomorph`, `d₅` times the library's generator at `S` is
the pull-back of the geometric generator of `ℝ⁵` at `S`'s coordinates (the class of the positive staircase cell,
`stair_generator_at`). -/
theorem geoGenerator_space (S : TernaryPoly.SymmetricSpacePositive.Space) :
    d5 • SymmetricSpaceLocalOrientation.localGenerator S =
      (SymmetricSpaceLocalOrientation.coordinateLocalHomologyIso S).inv
        (posOrientation5.generator (SymmetricSpaceEuclideanCoordinates.spaceHomeomorph S)) := by
  unfold SymmetricSpaceLocalOrientation.localGenerator
  change _ = (SymmetricSpaceLocalOrientation.coordinateLocalHomologyIso S).inv
    (d5 • localGenerator 3 (SymmetricSpaceEuclideanCoordinates.spaceHomeomorph S))
  rw [map_smul]

/-- **The flat is positively oriented in the log-pivot plane**: geometric local degree `+1` of the chart chain. -/
theorem geo_flat_positive : ∃ τ : ℚ, OrientTransport.flatDegree τ = 1 := by
  obtain ⟨κ, τ, -, -, h, -⟩ := Statements.Lemma33Geometric.apartment_orientation_sign
  exact ⟨τ, h⟩

/-- **The literal diagram in geometric orientations**: if `j_* c` is the class of the cellular top cycle `z`, then
`⟨PD^{geo}_∂ c, ∂a⟩ = -coeff_{T₀}(z)`, with the flat and its boundary (the coordinate apartment) untouched. -/
theorem geoDiagram_literal (W : Rep.{0} ℚ principalSix)
    (c : (SingularLocalHomology.boundaryLocalChains W).homology 3)
    (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0)
    (h : SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c =
      cellGroupHomologyMap W 3 (cellClass W z hz)) :
    flatBoundaryPairing W (PDboundaryGeo W c) = (-1 : ℚ) • (coeffAtT0 W).hom z := by
  have h1 := congrArg (fun f => f.hom c) (geoDiagram_commutes W)
  change groupApartmentEvaluationGeo W (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c) =
    flatBoundaryPairing W (PDboundaryGeo W c) at h1
  rw [← h1, h]
  exact geoEval_cell W z hz

/-- With the generator `T₀` reversed (`r = -1`) the geometric diagram reads the coefficient literally. -/
theorem geoDiagram_literal_reversed (W : Rep.{0} ℚ principalSix)
    (c : (SingularLocalHomology.boundaryLocalChains W).homology 3)
    (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0)
    (h : SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c =
      cellGroupHomologyMap W 3 (cellClass W z hz)) :
    flatBoundaryPairing W (PDboundaryGeo W c) = (coeffAtGen (-1) W).hom z := by
  rw [geoDiagram_literal W c z hz h, coeffAtGen_apply, inv_neg, inv_one]

end TernaryPeriodPolynomials.Argument.Lemma33.Geometric
