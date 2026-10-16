module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceMeasures

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic TopologicalSpace MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finitePlaceSplit_symm_measurePreserving (place : FinitePlace) :
    MeasurePreserving (finitePlaceSplit place).symm
      ((finiteCompletionMeasure place).prod (finiteAwayPlaceMeasure place)) finiteMeasure := by
  let productMeasure := (finiteCompletionMeasure place).prod (finiteAwayPlaceMeasure place)
  have mapped_haar : (Measure.map (finitePlaceSplit place).symm productMeasure).IsAddHaarMeasure :=
    (finitePlaceSplit place).symm.isAddHaarMeasure_map productMeasure
  let _ := mapped_haar
  have measurable : Measurable ((finitePlaceSplit place).symm :
      place.adicCompletion ℚ × FiniteAwayPlace place → FiniteAdeles) :=
    (finitePlaceSplit place).symm.continuous.measurable
  have normalized : Measure.map (finitePlaceSplit place).symm productMeasure
      (Set.range integralEmbedding) = 1 := by
    rw [Measure.map_apply measurable integralLattice_isOpen.measurableSet]
    have preimage : (finitePlaceSplit place).symm ⁻¹' Set.range integralEmbedding =
        (place.adicCompletionIntegers ℚ : Set (place.adicCompletion ℚ)) ×ˢ
          (Subtype.val ⁻¹' Set.range integralEmbedding) := by
      ext pair
      exact finitePlaceSplit_integral_iff place pair
    rw [preimage]
    change ((finiteCompletionMeasure place).prod (finiteAwayPlaceMeasure place)) _ = _
    rw [Measure.prod_prod, finiteCompletionMeasure_normalized,
      finiteAwayPlaceMeasure_normalized, mul_one]
  refine ⟨measurable, ?_⟩
  have unique := Measure.addHaarMeasure_unique
    (Measure.map (finitePlaceSplit place).symm productMeasure) finiteUnitCompact
  change Measure.map (finitePlaceSplit place).symm productMeasure = Measure.addHaarMeasure finiteUnitCompact
  simpa only [show (finiteUnitCompact : Set FiniteAdeles) = Set.range integralEmbedding from rfl,
    normalized, one_smul] using unique

theorem finitePlaceSplit_measurePreserving (place : FinitePlace) :
    MeasurePreserving (finitePlaceSplit place) finiteMeasure
      ((finiteCompletionMeasure place).prod (finiteAwayPlaceMeasure place)) :=
  MeasurePreserving.symm (finitePlaceSplit place).symm.toHomeomorph.toMeasurableEquiv
    (finitePlaceSplit_symm_measurePreserving place)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
