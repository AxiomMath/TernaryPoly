module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlanePivotAssembly

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem standardGoodLineFiniteArgument_pivot (finite : FiniteAwayThree × FiniteAwayThree) :
    standardGoodLineFiniteArgument finite = planeOppositeStandardMatrix finite.1.val finite.2.val :=
  Units.ext (standardGoodLineFiniteArgument_val finite)

def standardGoodLineFinitePivotCoordinates (finite : FiniteAwayThree × FiniteAwayThree) :
    FinitePlaneInductionCoordinates (standardGoodLineFiniteArgument finite) :=
  let coordinates := finitePlanePivotCoordinates finite.1.val finite.2.val
  { first := coordinates.first
    second := coordinates.second
    scalar := coordinates.scalar
    block := coordinates.block
    compact := coordinates.compact
    factorization := (standardGoodLineFiniteArgument_pivot finite).trans coordinates.factorization }

theorem standardGoodLineFinitePivotCoordinates_block (finite : FiniteAwayThree × FiniteAwayThree)
    (place : FinitePlace) :
    GeneralLinearGroup.map (finiteEvaluation place) (standardGoodLineFinitePivotCoordinates finite).block =
      (finitePlanePivotLocalCoordinates finite.1.val finite.2.val place).block :=
  finitePlanePivotCoordinates_block_eval _ _ place

theorem standardGoodLineFinitePivotCoordinates_det (finite : FiniteAwayThree × FiniteAwayThree)
    (place : FinitePlace) :
    Valued.v (finiteEvaluation place (GeneralLinearGroup.det
      (standardGoodLineFinitePivotCoordinates finite).block).val) =
      (max 1 (max (Valued.v (finiteEvaluation place finite.1.val))
        (Valued.v (finiteEvaluation place finite.2.val))))⁻¹ := by
  have determinants := congrArg (fun matrix : GeneralLinearGroup (Fin 2) (place.adicCompletion ℚ) =>
    (GeneralLinearGroup.det matrix).val) (standardGoodLineFinitePivotCoordinates_block finite place)
  rw [generalLinearGroup_det_map] at determinants
  change finiteEvaluation place (GeneralLinearGroup.det
    (standardGoodLineFinitePivotCoordinates finite).block).val = _ at determinants
  rw [determinants]
  exact valuedPlanePivotCoordinates_det Valued.v _ _

theorem standardGoodLineFinitePivotCoordinates_block_integral
    (finite : FiniteAwayThree × FiniteAwayThree) (place : FinitePlace)
    (first_integral : Valued.v (finiteEvaluation place finite.1.val) ≤ 1)
    (second_integral : Valued.v (finiteEvaluation place finite.2.val) ≤ 1) :
    GeneralLinearGroup.map (finiteEvaluation place) (standardGoodLineFinitePivotCoordinates finite).block = 1 := by
  rw [standardGoodLineFinitePivotCoordinates_block]
  change (valuedPlanePivotCoordinates Valued.v _ _).block = 1
  rw [valuedPlanePivotCoordinates_integral Valued.v _ _ first_integral second_integral]
  rfl

theorem standardGoodLineFinitePivotCoordinates_block_first
    (finite : FiniteAwayThree × FiniteAwayThree) (place : FinitePlace)
    (large : 1 < Valued.v (finiteEvaluation place finite.1.val))
    (dominant : Valued.v (finiteEvaluation place finite.2.val) ≤
      Valued.v (finiteEvaluation place finite.1.val)) :
    GeneralLinearGroup.map (finiteEvaluation place) (standardGoodLineFinitePivotCoordinates finite).block =
      planeFirstPivotBinary (Units.mk0 (finiteEvaluation place finite.1.val)
        (valuation_pivot_ne_zero Valued.v large)) (finiteEvaluation place finite.2.val) := by
  rw [standardGoodLineFinitePivotCoordinates_block]
  change (valuedPlanePivotCoordinates Valued.v _ _).block = _
  rw [valuedPlanePivotCoordinates_first Valued.v _ _ large dominant]
  rfl

theorem standardGoodLineFinitePivotCoordinates_block_second
    (finite : FiniteAwayThree × FiniteAwayThree) (place : FinitePlace)
    (large : 1 < Valued.v (finiteEvaluation place finite.2.val))
    (dominant : Valued.v (finiteEvaluation place finite.1.val) <
      Valued.v (finiteEvaluation place finite.2.val)) :
    GeneralLinearGroup.map (finiteEvaluation place) (standardGoodLineFinitePivotCoordinates finite).block =
      planeSecondPivotBinary (Units.mk0 (finiteEvaluation place finite.2.val)
        (valuation_pivot_ne_zero Valued.v large)) (finiteEvaluation place finite.1.val) := by
  rw [standardGoodLineFinitePivotCoordinates_block]
  change (valuedPlanePivotCoordinates Valued.v _ _).block = _
  rw [valuedPlanePivotCoordinates_second Valued.v _ _ large dominant]
  rfl

/-- The actual finite average can be computed with the explicit local pivot choices. -/
theorem goodLineFiniteVectorIntegral_pivot (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    goodLineFiniteVectorIntegral degree cusp parameter vector =
      ∫ finite : FiniteAwayThree × FiniteAwayThree,
        normPower (finiteAdeleUnit (GeneralLinearGroup.det
          (standardGoodLineFinitePivotCoordinates finite).block)) ((degree : ℂ) / 2 + 3 + parameter) *
        cusp.realize vector (atFinite (standardGoodLineFinitePivotCoordinates finite).block)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) :=
  goodLineFiniteVectorIntegral_eq_coordinates degree cusp parameter vector spherical
    standardGoodLineFinitePivotCoordinates

end TernaryPeriodPolynomials.SphericalDetection.Helpers
