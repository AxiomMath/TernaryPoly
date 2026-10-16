module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteEulerFactor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finiteIntegralOutside (places : Finset FinitePlace) : Set FiniteAdeles :=
  {value | ∀ place, place ∉ places → finiteEvaluation place value ∈ place.adicCompletionIntegers ℚ}

theorem finiteIntegralOutside_measurable (places : Finset FinitePlace) :
    MeasurableSet (finiteIntegralOutside places) := by
  unfold finiteIntegralOutside
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro place
  apply MeasurableSet.iInter
  intro _
  have evaluation : Continuous (fun value : FiniteAdeles => finiteEvaluation place value) :=
    RestrictedProduct.continuous_eval place
  exact (Valued.isOpen_valuationSubring (place.adicCompletion ℚ)).measurableSet.preimage evaluation.measurable

theorem finiteIntegralOutside_mono : Monotone finiteIntegralOutside := by
  intro first second included value integral place outside
  exact integral place (fun member => outside (included member))

theorem finiteIntegralOutside_empty : finiteIntegralOutside ∅ = Set.range integralEmbedding := by
  ext value
  constructor
  · intro integral
    refine ⟨fun place => ⟨finiteEvaluation place value, integral place (by simp)⟩, ?_⟩
    apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
    intro place
    rfl
  · rintro ⟨integral, rfl⟩ place _
    exact (integral place).property

theorem finiteIntegralOutside_union : (⋃ places, finiteIntegralOutside places) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro value
  have eventually := RestrictedProduct.eventually
    (fun place : FinitePlace => place.adicCompletion ℚ)
    (fun place : FinitePlace => (place.adicCompletionIntegers ℚ : Set (place.adicCompletion ℚ))) value
  have finite : {place : FinitePlace | finiteEvaluation place value ∉ place.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp eventually
  refine Set.mem_iUnion.mpr ⟨finite.toFinset, ?_⟩
  intro place outside
  by_contra not_integral
  exact outside (finite.mem_toFinset.mpr not_integral)

def goodLineFiniteSupportRegion (places : Finset FinitePlace) : Set (FiniteAwayThree × FiniteAwayThree) :=
  {pair | pair.1.val ∈ finiteIntegralOutside places ∧ pair.2.val ∈ finiteIntegralOutside places}

theorem goodLineFiniteSupportRegion_measurable (places : Finset FinitePlace) :
    MeasurableSet (goodLineFiniteSupportRegion places) := by
  exact ((finiteIntegralOutside_measurable places).preimage
    (continuous_subtype_val.comp continuous_fst).measurable).inter
    ((finiteIntegralOutside_measurable places).preimage
      (continuous_subtype_val.comp continuous_snd).measurable)

theorem goodLineFiniteSupportRegion_mono : Monotone goodLineFiniteSupportRegion := by
  intro first second included pair member
  exact ⟨finiteIntegralOutside_mono included member.1, finiteIntegralOutside_mono included member.2⟩

theorem goodLineFiniteSupportRegion_empty : goodLineFiniteSupportRegion ∅ =
    (Subtype.val ⁻¹' Set.range integralEmbedding) ×ˢ (Subtype.val ⁻¹' Set.range integralEmbedding) := by
  ext pair
  simp only [goodLineFiniteSupportRegion, Set.mem_ofPred_eq, finiteIntegralOutside_empty,
    Set.mem_prod, Set.mem_preimage]

theorem goodLineFiniteSupportRegion_union : (⋃ places, goodLineFiniteSupportRegion places) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro pair
  have first : pair.1.val ∈ ⋃ places, finiteIntegralOutside places := by rw [finiteIntegralOutside_union]; trivial
  have second : pair.2.val ∈ ⋃ places, finiteIntegralOutside places := by rw [finiteIntegralOutside_union]; trivial
  obtain ⟨first_places, first_integral⟩ := Set.mem_iUnion.mp first
  obtain ⟨second_places, second_integral⟩ := Set.mem_iUnion.mp second
  exact Set.mem_iUnion.mpr ⟨first_places ∪ second_places,
    finiteIntegralOutside_mono Finset.subset_union_left first_integral,
    finiteIntegralOutside_mono Finset.subset_union_right second_integral⟩

theorem goodLineFiniteSupportRegion_integral_tendsto (value : FiniteAwayThree × FiniteAwayThree → ℂ)
    (integrable : Integrable value (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    Tendsto (fun places : Finset FinitePlace =>
      ∫ pair in goodLineFiniteSupportRegion places, value pair ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) atTop
      (nhds (∫ pair, value pair ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))) := by
  have limit := tendsto_setIntegral_of_monotone goodLineFiniteSupportRegion_measurable goodLineFiniteSupportRegion_mono
    (show IntegrableOn value (⋃ places, goodLineFiniteSupportRegion places)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) by
      rw [goodLineFiniteSupportRegion_union]
      exact integrable.integrableOn)
  simpa only [goodLineFiniteSupportRegion_union, setIntegral_univ] using limit

end TernaryPeriodPolynomials.SphericalDetection.Helpers
