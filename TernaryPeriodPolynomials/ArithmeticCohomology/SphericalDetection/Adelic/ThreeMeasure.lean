module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.ThreeSplitting
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Local.Detection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TopologicalSpace MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finiteAwayThree_isClosed : IsClosed (finiteThree.toAddMonoidHom.ker : Set FiniteAdeles) :=
  isClosed_eq finiteThree_continuous continuous_const

instance finiteAwayThreeLocallyCompact : LocallyCompactSpace FiniteAwayThree :=
  finiteAwayThree_isClosed.locallyCompactSpace

instance finiteAwayThreeSecondCountable : SecondCountableTopology FiniteAwayThree :=
  finiteAwayThree_isClosed.isClosedEmbedding_subtypeVal.isEmbedding.isInducing.secondCountableTopology

def finiteAwayThreeUnitCompact : PositiveCompacts FiniteAwayThree where
  carrier := Subtype.val ⁻¹' Set.range integralEmbedding
  isCompact' := finiteAwayThree_isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    integralLattice_isCompact
  interior_nonempty' := by
    rw [(integralLattice_isOpen.preimage continuous_subtype_val).interior_eq]
    exact ⟨0, 0, map_zero integralEmbedding⟩

def finiteAwayThreeMeasure : Measure FiniteAwayThree :=
  Measure.addHaarMeasure finiteAwayThreeUnitCompact

instance finiteAwayThreeMeasure_haar : finiteAwayThreeMeasure.IsAddHaarMeasure :=
  inferInstanceAs ((Measure.addHaarMeasure finiteAwayThreeUnitCompact).IsAddHaarMeasure)

instance finiteAwayThreeMeasure_sigmaFinite : SigmaFinite finiteAwayThreeMeasure :=
  inferInstanceAs (SigmaFinite (Measure.addHaarMeasure finiteAwayThreeUnitCompact))

theorem finiteAwayThreeMeasure_normalized :
    finiteAwayThreeMeasure (Subtype.val ⁻¹' Set.range integralEmbedding) = 1 :=
  Measure.addHaarMeasure_self

theorem finiteThreeSplit_integral_iff (pair : ℚ_[3] × FiniteAwayThree) :
    finiteThreeSplit.symm pair ∈ Set.range integralEmbedding ↔
      ‖pair.1‖ ≤ 1 ∧ pair.2.val ∈ Set.range integralEmbedding := by
  rw [finiteThreeSplit_symm]
  constructor
  · rintro ⟨integer, equality⟩
    have at_three : (integralThree integer : ℚ_[3]) = pair.1 := by
      have away_zero : finiteThree pair.2.val = 0 := pair.2.property
      have equal := congrArg finiteThree equality
      rwa [finiteThree_integral, map_add, finiteAtThreeScalar_three, away_zero, add_zero] at equal
    have local_integral : ‖pair.1‖ ≤ 1 := by
      rw [← at_three]
      exact (integralThree integer).property
    refine ⟨local_integral, ?_⟩
    have embedded := finiteAtThreeScalar_integral (⟨pair.1, local_integral⟩ : ℤ_[3])
    have original : finiteAtThreeScalar pair.1 + pair.2.val ∈ integralEmbedding.range :=
      ⟨integer, equality⟩
    have difference := integralEmbedding.range.sub_mem original embedded
    simp only [add_sub_cancel_left] at difference
    exact difference
  · rintro ⟨local_integral, away_integral⟩
    exact integralEmbedding.range.add_mem
      (finiteAtThreeScalar_integral (⟨pair.1, local_integral⟩ : ℤ_[3])) away_integral

local instance normalizedThreeHaar : normalizedLocalThreeMeasure.IsAddHaarMeasure :=
  normalizedLocalThreeMeasure_haar

theorem finiteThreeSplit_symm_measurePreserving :
    MeasurePreserving finiteThreeSplit.symm
      (normalizedLocalThreeMeasure.prod finiteAwayThreeMeasure) finiteMeasure := by
  let productMeasure := normalizedLocalThreeMeasure.prod finiteAwayThreeMeasure
  have mapped_haar : (Measure.map finiteThreeSplit.symm productMeasure).IsAddHaarMeasure :=
    finiteThreeSplit.symm.isAddHaarMeasure_map productMeasure
  let _ := mapped_haar
  have measurable : Measurable (finiteThreeSplit.symm : ℚ_[3] × FiniteAwayThree → FiniteAdeles) :=
    finiteThreeSplit.symm.continuous.measurable
  have normalized : Measure.map finiteThreeSplit.symm productMeasure
      (Set.range integralEmbedding) = 1 := by
    rw [Measure.map_apply measurable integralLattice_isOpen.measurableSet]
    have preimage : finiteThreeSplit.symm ⁻¹' Set.range integralEmbedding =
        {value : ℚ_[3] | ‖value‖ ≤ 1} ×ˢ (Subtype.val ⁻¹' Set.range integralEmbedding) := by
      ext pair
      exact finiteThreeSplit_integral_iff pair
    rw [preimage]
    change (normalizedLocalThreeMeasure.prod finiteAwayThreeMeasure) _ = _
    rw [Measure.prod_prod, normalizedLocalThreeMeasure_normalized,
      finiteAwayThreeMeasure_normalized, mul_one]
  refine ⟨measurable, ?_⟩
  have unique := Measure.addHaarMeasure_unique
    (Measure.map finiteThreeSplit.symm productMeasure) finiteUnitCompact
  change Measure.map finiteThreeSplit.symm productMeasure = Measure.addHaarMeasure finiteUnitCompact
  simpa only [show (finiteUnitCompact : Set FiniteAdeles) = Set.range integralEmbedding from rfl,
    normalized, one_smul] using unique

theorem finiteThreeSplit_measurePreserving :
    MeasurePreserving finiteThreeSplit finiteMeasure
      (normalizedLocalThreeMeasure.prod finiteAwayThreeMeasure) :=
  MeasurePreserving.symm finiteThreeSplit.symm.toHomeomorph.toMeasurableEquiv
    finiteThreeSplit_symm_measurePreserving

end TernaryPeriodPolynomials.SphericalDetection.Helpers
