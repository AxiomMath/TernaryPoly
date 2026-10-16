module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceSplitting

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic TopologicalSpace MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

instance finiteCompletionMeasurableSpace (place : FinitePlace) : MeasurableSpace (place.adicCompletion ℚ) :=
  borel (place.adicCompletion ℚ)

instance finiteCompletionBorelSpace (place : FinitePlace) : BorelSpace (place.adicCompletion ℚ) := ⟨rfl⟩

def finiteCompletionUnitCompact (place : FinitePlace) : PositiveCompacts (place.adicCompletion ℚ) where
  carrier := place.adicCompletionIntegers ℚ
  isCompact' := isCompact_iff_compactSpace.mpr
    (inferInstanceAs (CompactSpace (place.adicCompletionIntegers ℚ)))
  interior_nonempty' := by
    have open_integer : IsOpen (place.adicCompletionIntegers ℚ : Set (place.adicCompletion ℚ)) :=
      Valued.isOpen_valuationSubring _
    rw [open_integer.interior_eq]
    exact ⟨0, zero_mem _⟩

def finiteCompletionMeasure (place : FinitePlace) : Measure (place.adicCompletion ℚ) :=
  Measure.addHaarMeasure (finiteCompletionUnitCompact place)

instance finiteCompletionMeasure_haar (place : FinitePlace) : (finiteCompletionMeasure place).IsAddHaarMeasure :=
  inferInstanceAs ((Measure.addHaarMeasure (finiteCompletionUnitCompact place)).IsAddHaarMeasure)

instance finiteCompletionMeasure_sigmaFinite (place : FinitePlace) : SigmaFinite (finiteCompletionMeasure place) :=
  inferInstanceAs (SigmaFinite (Measure.addHaarMeasure (finiteCompletionUnitCompact place)))

theorem finiteCompletionMeasure_normalized (place : FinitePlace) :
    finiteCompletionMeasure place (place.adicCompletionIntegers ℚ) = 1 :=
  Measure.addHaarMeasure_self

theorem finiteAwayPlace_isClosed (place : FinitePlace) : IsClosed (FiniteAwayPlace place : Set FiniteAdeles) :=
  isClosed_eq (RestrictedProduct.continuous_eval place) continuous_const

instance finiteAwayPlaceLocallyCompact (place : FinitePlace) : LocallyCompactSpace (FiniteAwayPlace place) :=
  (finiteAwayPlace_isClosed place).locallyCompactSpace

instance finiteAwayPlaceSecondCountable (place : FinitePlace) : SecondCountableTopology (FiniteAwayPlace place) :=
  (finiteAwayPlace_isClosed place).isClosedEmbedding_subtypeVal.isEmbedding.isInducing.secondCountableTopology

def finiteAwayPlaceUnitCompact (place : FinitePlace) : PositiveCompacts (FiniteAwayPlace place) where
  carrier := Subtype.val ⁻¹' Set.range integralEmbedding
  isCompact' := (finiteAwayPlace_isClosed place).isClosedEmbedding_subtypeVal.isCompact_preimage
    integralLattice_isCompact
  interior_nonempty' := by
    rw [(integralLattice_isOpen.preimage continuous_subtype_val).interior_eq]
    exact ⟨0, 0, map_zero integralEmbedding⟩

def finiteAwayPlaceMeasure (place : FinitePlace) : Measure (FiniteAwayPlace place) :=
  Measure.addHaarMeasure (finiteAwayPlaceUnitCompact place)

instance finiteAwayPlaceMeasure_haar (place : FinitePlace) : (finiteAwayPlaceMeasure place).IsAddHaarMeasure :=
  inferInstanceAs ((Measure.addHaarMeasure (finiteAwayPlaceUnitCompact place)).IsAddHaarMeasure)

instance finiteAwayPlaceMeasure_sigmaFinite (place : FinitePlace) : SigmaFinite (finiteAwayPlaceMeasure place) :=
  inferInstanceAs (SigmaFinite (Measure.addHaarMeasure (finiteAwayPlaceUnitCompact place)))

theorem finiteAwayPlaceMeasure_normalized (place : FinitePlace) :
    finiteAwayPlaceMeasure place (Subtype.val ⁻¹' Set.range integralEmbedding) = 1 :=
  Measure.addHaarMeasure_self

theorem finitePlaceSplit_integral_iff (place : FinitePlace) (pair : place.adicCompletion ℚ × FiniteAwayPlace place) :
    (finitePlaceSplit place).symm pair ∈ Set.range integralEmbedding ↔
      pair.1 ∈ place.adicCompletionIntegers ℚ ∧ pair.2.val ∈ Set.range integralEmbedding := by
  rw [finitePlaceSplit_symm]
  constructor
  · rintro ⟨integer, equality⟩
    have local_eq : (integer place).val = pair.1 := by
      have away_zero : finiteEvaluation place pair.2.val = 0 := pair.2.property
      have equal := congrArg (finiteEvaluation place) equality
      rwa [integralEmbedding_at, map_add, finiteAtPlaceScalar_same, away_zero, add_zero] at equal
    have local_integral : pair.1 ∈ place.adicCompletionIntegers ℚ := local_eq ▸ (integer place).property
    refine ⟨local_integral, ?_⟩
    have embedded := finiteAtPlaceScalar_integral place ⟨pair.1, local_integral⟩
    have original : finiteAtPlaceScalar place pair.1 + pair.2.val ∈ integralEmbedding.range := ⟨integer, equality⟩
    have difference := integralEmbedding.range.sub_mem original embedded
    simp only [add_sub_cancel_left] at difference
    exact difference
  · rintro ⟨local_integral, away_integral⟩
    exact integralEmbedding.range.add_mem (finiteAtPlaceScalar_integral place ⟨pair.1, local_integral⟩) away_integral

end TernaryPeriodPolynomials.SphericalDetection.Helpers
