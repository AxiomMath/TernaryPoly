module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.AwayThreePlaceSplitting

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic TopologicalSpace MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finiteAwayThreePlace_isClosed (place : FinitePlace) :
    IsClosed (FiniteAwayThreePlace place : Set FiniteAwayThree) :=
  isClosed_eq (finiteAwayThreeEvaluation_continuous place) continuous_const

instance finiteAwayThreePlaceLocallyCompact (place : FinitePlace) : LocallyCompactSpace (FiniteAwayThreePlace place) :=
  (finiteAwayThreePlace_isClosed place).locallyCompactSpace

instance finiteAwayThreePlaceSecondCountable (place : FinitePlace) : SecondCountableTopology (FiniteAwayThreePlace place) :=
  (finiteAwayThreePlace_isClosed place).isClosedEmbedding_subtypeVal.isEmbedding.isInducing.secondCountableTopology

def finiteAwayThreePlaceUnitCompact (place : FinitePlace) : PositiveCompacts (FiniteAwayThreePlace place) where
  carrier := (fun value => value.val.val) ⁻¹' Set.range integralEmbedding
  isCompact' := (finiteAwayThreePlace_isClosed place).isClosedEmbedding_subtypeVal.isCompact_preimage
    finiteAwayThreeUnitCompact.isCompact
  interior_nonempty' := by
    have open_set : IsOpen ((fun value : FiniteAwayThreePlace place => value.val.val) ⁻¹' Set.range integralEmbedding) :=
      integralLattice_isOpen.preimage (continuous_subtype_val.comp continuous_subtype_val)
    rw [open_set.interior_eq]
    exact ⟨0, 0, map_zero integralEmbedding⟩

def finiteAwayThreePlaceMeasure (place : FinitePlace) : Measure (FiniteAwayThreePlace place) :=
  Measure.addHaarMeasure (finiteAwayThreePlaceUnitCompact place)

instance finiteAwayThreePlaceMeasure_haar (place : FinitePlace) : (finiteAwayThreePlaceMeasure place).IsAddHaarMeasure :=
  inferInstanceAs ((Measure.addHaarMeasure (finiteAwayThreePlaceUnitCompact place)).IsAddHaarMeasure)

instance finiteAwayThreePlaceMeasure_sigmaFinite (place : FinitePlace) : SigmaFinite (finiteAwayThreePlaceMeasure place) :=
  inferInstanceAs (SigmaFinite (Measure.addHaarMeasure (finiteAwayThreePlaceUnitCompact place)))

theorem finiteAwayThreePlaceMeasure_normalized (place : FinitePlace) :
    finiteAwayThreePlaceMeasure place ((fun value => value.val.val) ⁻¹' Set.range integralEmbedding) = 1 :=
  Measure.addHaarMeasure_self

theorem finiteAwayThreePlaceSplit_integral_iff (place : FinitePlace) (distinct : place ≠ placeThree)
    (pair : place.adicCompletion ℚ × FiniteAwayThreePlace place) :
    ((finiteAwayThreePlaceSplit place distinct).symm pair).val ∈ Set.range integralEmbedding ↔
      pair.1 ∈ place.adicCompletionIntegers ℚ ∧ pair.2.val.val ∈ Set.range integralEmbedding := by
  rw [finiteAwayThreePlaceSplit_symm_val]
  constructor
  · rintro ⟨integer, equality⟩
    have local_eq : (integer place).val = pair.1 := by
      have away_zero : finiteEvaluation place pair.2.val.val = 0 := pair.2.property
      have equal := congrArg (finiteEvaluation place) equality
      rwa [integralEmbedding_at, map_add, finiteAtPlaceScalar_same, away_zero, add_zero] at equal
    have local_integral : pair.1 ∈ place.adicCompletionIntegers ℚ := local_eq ▸ (integer place).property
    refine ⟨local_integral, ?_⟩
    have embedded := finiteAtPlaceScalar_integral place ⟨pair.1, local_integral⟩
    have original : finiteAtPlaceScalar place pair.1 + pair.2.val.val ∈ integralEmbedding.range := ⟨integer, equality⟩
    have difference := integralEmbedding.range.sub_mem original embedded
    simp only [add_sub_cancel_left] at difference
    exact difference
  · rintro ⟨local_integral, away_integral⟩
    exact integralEmbedding.range.add_mem (finiteAtPlaceScalar_integral place ⟨pair.1, local_integral⟩) away_integral

theorem finiteAwayThreePlaceSplit_symm_measurePreserving (place : FinitePlace) (distinct : place ≠ placeThree) :
    MeasurePreserving (finiteAwayThreePlaceSplit place distinct).symm
      ((finiteCompletionMeasure place).prod (finiteAwayThreePlaceMeasure place)) finiteAwayThreeMeasure := by
  let productMeasure := (finiteCompletionMeasure place).prod (finiteAwayThreePlaceMeasure place)
  have mapped_haar : (Measure.map (finiteAwayThreePlaceSplit place distinct).symm productMeasure).IsAddHaarMeasure :=
    (finiteAwayThreePlaceSplit place distinct).symm.isAddHaarMeasure_map productMeasure
  let _ := mapped_haar
  have measurable : Measurable ((finiteAwayThreePlaceSplit place distinct).symm :
      place.adicCompletion ℚ × FiniteAwayThreePlace place → FiniteAwayThree) :=
    (finiteAwayThreePlaceSplit place distinct).symm.continuous.measurable
  have normalized : Measure.map (finiteAwayThreePlaceSplit place distinct).symm productMeasure
      (Subtype.val ⁻¹' Set.range integralEmbedding) = 1 := by
    rw [Measure.map_apply measurable (integralLattice_isOpen.preimage continuous_subtype_val).measurableSet]
    have preimage : (finiteAwayThreePlaceSplit place distinct).symm ⁻¹'
        (Subtype.val ⁻¹' Set.range integralEmbedding) =
        (place.adicCompletionIntegers ℚ : Set (place.adicCompletion ℚ)) ×ˢ
          ((fun value => value.val.val) ⁻¹' Set.range integralEmbedding) := by
      ext pair
      exact finiteAwayThreePlaceSplit_integral_iff place distinct pair
    rw [preimage]
    change ((finiteCompletionMeasure place).prod (finiteAwayThreePlaceMeasure place)) _ = _
    rw [Measure.prod_prod, finiteCompletionMeasure_normalized, finiteAwayThreePlaceMeasure_normalized, mul_one]
  refine ⟨measurable, ?_⟩
  have unique := Measure.addHaarMeasure_unique
    (Measure.map (finiteAwayThreePlaceSplit place distinct).symm productMeasure) finiteAwayThreeUnitCompact
  change Measure.map (finiteAwayThreePlaceSplit place distinct).symm productMeasure =
    Measure.addHaarMeasure finiteAwayThreeUnitCompact
  simpa only [show (finiteAwayThreeUnitCompact : Set FiniteAwayThree) =
      Subtype.val ⁻¹' Set.range integralEmbedding from rfl, normalized, one_smul] using unique

theorem finiteAwayThreePlaceSplit_measurePreserving (place : FinitePlace) (distinct : place ≠ placeThree) :
    MeasurePreserving (finiteAwayThreePlaceSplit place distinct) finiteAwayThreeMeasure
      ((finiteCompletionMeasure place).prod (finiteAwayThreePlaceMeasure place)) :=
  MeasurePreserving.symm (finiteAwayThreePlaceSplit place distinct).symm.toHomeomorph.toMeasurableEquiv
    (finiteAwayThreePlaceSplit_symm_measurePreserving place distinct)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
