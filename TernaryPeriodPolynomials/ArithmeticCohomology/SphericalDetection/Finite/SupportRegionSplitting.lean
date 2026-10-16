module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.SupportRegions

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance finiteSupportRegionDecidableEq : DecidableEq FinitePlace := Classical.decEq _

theorem finiteIntegralOutside_add_single (places : Finset FinitePlace) (place : FinitePlace)
    (localValue : place.adicCompletion ℚ) (away : FiniteAdeles) (zero : finiteEvaluation place away = 0) :
    finiteAtPlaceScalar place localValue + away ∈ finiteIntegralOutside places ↔
      (place ∉ places → localValue ∈ place.adicCompletionIntegers ℚ) ∧ away ∈ finiteIntegralOutside places := by
  constructor
  · intro integral
    constructor
    · intro outside
      have member := integral place outside
      rwa [map_add, finiteAtPlaceScalar_same, zero, add_zero] at member
    · intro other outside
      by_cases same : other = place
      · subst other
        rw [zero]
        exact zero_mem _
      · have member := integral other outside
        rwa [map_add, finiteAtPlaceScalar_away _ _ _ same, zero_add] at member
  · rintro ⟨local_integral, away_integral⟩ other outside
    by_cases same : other = place
    · subst other
      rw [map_add, finiteAtPlaceScalar_same, zero, add_zero]
      exact local_integral outside
    · rw [map_add, finiteAtPlaceScalar_away _ _ _ same, zero_add]
      exact away_integral other outside

theorem finiteIntegralOutside_insert_zero (places : Finset FinitePlace) (place : FinitePlace)
    (away : FiniteAdeles) (zero : finiteEvaluation place away = 0) :
    away ∈ finiteIntegralOutside (insert place places) ↔ away ∈ finiteIntegralOutside places := by
  classical
  constructor
  · intro integral other outside
    by_cases same : other = place
    · subst other
      rw [zero]
      exact zero_mem _
    · exact integral other (by simp only [Finset.mem_insert]; tauto)
  · exact fun integral => finiteIntegralOutside_mono (Finset.subset_insert _ _) integral

theorem finiteIntegralOutside_padic_join (places : Finset FinitePlace) (place : FinitePlace)
    (distinct : place ≠ placeThree) (outside : place ∉ places) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localValue : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) (away : FiniteAwayThreePlace place),
      ((finiteAwayThreePadicSplit place distinct).symm (localValue, away)).val ∈ finiteIntegralOutside places ↔
        ‖localValue‖ ≤ 1 ∧ away.val.val ∈ finiteIntegralOutside places := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localValue away
  rw [finiteAwayThreePadicSplit_symm_val]
  dsimp only
  rw [finiteIntegralOutside_add_single _ place _ away.val.val (show finiteEvaluation place away.val.val = 0 from away.property)]
  simp only [outside, not_false_eq_true, true_implies]
  rw [← finiteCompletionPadic_integral_iff, RingEquiv.apply_symm_apply]

theorem finiteIntegralOutside_padic_join_insert (places : Finset FinitePlace) (place : FinitePlace)
    (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localValue : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) (away : FiniteAwayThreePlace place),
      ((finiteAwayThreePadicSplit place distinct).symm (localValue, away)).val ∈ finiteIntegralOutside (insert place places) ↔
        away.val.val ∈ finiteIntegralOutside places := by
  classical
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localValue away
  rw [finiteAwayThreePadicSplit_symm_val]
  dsimp only
  rw [finiteIntegralOutside_add_single _ place _ away.val.val (show finiteEvaluation place away.val.val = 0 from away.property)]
  simp only [Finset.mem_insert_self, not_true_eq_false, false_implies, true_and]
  exact finiteIntegralOutside_insert_zero places place away.val.val (show finiteEvaluation place away.val.val = 0 from away.property)

def goodLineAwayPlaceSupportRegion (place : FinitePlace) (places : Finset FinitePlace) :
    Set (FiniteAwayThreePlace place × FiniteAwayThreePlace place) :=
  {pair | pair.1.val.val ∈ finiteIntegralOutside places ∧ pair.2.val.val ∈ finiteIntegralOutside places}

theorem goodLineAwayPlaceSupportRegion_measurable (place : FinitePlace) (places : Finset FinitePlace) :
    MeasurableSet (goodLineAwayPlaceSupportRegion place places) := by
  exact ((finiteIntegralOutside_measurable places).preimage
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).measurable).inter
    ((finiteIntegralOutside_measurable places).preimage
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).measurable)

theorem goodLineFiniteSupportRegion_padic_preimage (places : Finset FinitePlace) (place : FinitePlace)
    (distinct : place ≠ placeThree) (outside : place ∉ places) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (finiteAwayThreePadicRadicalJoin place distinct) ⁻¹' goodLineFiniteSupportRegion places =
      {pair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] |
        ‖pair.1‖ ≤ 1 ∧ ‖pair.2‖ ≤ 1} ×ˢ goodLineAwayPlaceSupportRegion place places := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  ext pair
  simp only [Set.mem_preimage, goodLineFiniteSupportRegion, Set.mem_ofPred_eq,
    finiteAwayThreePadicRadicalJoin_apply, finiteIntegralOutside_padic_join _ _ distinct outside,
    Set.mem_prod, goodLineAwayPlaceSupportRegion]
  tauto

theorem goodLineFiniteSupportRegion_padic_preimage_insert (places : Finset FinitePlace) (place : FinitePlace)
    (distinct : place ≠ placeThree) :
    (finiteAwayThreePadicRadicalJoin place distinct) ⁻¹' goodLineFiniteSupportRegion (insert place places) =
      Set.univ ×ˢ goodLineAwayPlaceSupportRegion place places := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  ext pair
  simp only [Set.mem_preimage, goodLineFiniteSupportRegion, Set.mem_ofPred_eq,
    finiteAwayThreePadicRadicalJoin_apply, finiteIntegralOutside_padic_join_insert,
    Set.mem_prod, goodLineAwayPlaceSupportRegion, Set.mem_univ, true_and]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
