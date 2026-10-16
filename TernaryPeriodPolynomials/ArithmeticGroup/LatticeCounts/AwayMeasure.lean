module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.AwayStep

@[expose] public section


/-!
# Haar measures on `awayS S` and the one-step measure split

Formalized by Claude Haiku 5.5.

For a finite set `S` of places (not containing `3`), `awayS S` carries the additive Haar measure
normalised so that the integral points have measure one (`awayMeasure S`). The one-step split
`awayStepSplit` is measure preserving from `finiteCompletionMeasure q ⊗ awayMeasure T` to
`awayMeasure S` (`T = S ∪ {q}`), the restriction of the one-place theorem
`finiteAwayThreePlaceSplit_symm_measurePreserving`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic TopologicalSpace MeasureTheory

noncomputable section

local instance awayMeasureDecidableEq : DecidableEq FinitePlace := Classical.decEq _

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayStep

theorem awayS_isClosed (S : Finset FinitePlace) : IsClosed ((awayS S : AddSubgroup FiniteAwayThree) : Set FiniteAwayThree) := by
  have eq : ((awayS S : AddSubgroup FiniteAwayThree) : Set FiniteAwayThree) =
      ⋂ p ∈ S, {x | finiteAwayThreeEvaluation p x = 0} := by
    ext x
    simp only [SetLike.mem_coe, mem_awayS, Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [eq]
  exact isClosed_biInter fun p _ => isClosed_eq (finiteAwayThreeEvaluation_continuous p) continuous_const

instance awayS_locallyCompact (S : Finset FinitePlace) : LocallyCompactSpace (awayS S) :=
  (awayS_isClosed S).locallyCompactSpace

instance awayS_secondCountable (S : Finset FinitePlace) : SecondCountableTopology (awayS S) :=
  (awayS_isClosed S).isClosedEmbedding_subtypeVal.isEmbedding.isInducing.secondCountableTopology

/-- The integral points of `awayS S`. -/
def awayUnitCompact (S : Finset FinitePlace) : PositiveCompacts (awayS S) where
  carrier := (fun value : awayS S => value.val.val) ⁻¹' Set.range integralEmbedding
  isCompact' := (awayS_isClosed S).isClosedEmbedding_subtypeVal.isCompact_preimage
    finiteAwayThreeUnitCompact.isCompact
  interior_nonempty' := by
    have open_set : IsOpen ((fun value : awayS S => value.val.val) ⁻¹' Set.range integralEmbedding) :=
      integralLattice_isOpen.preimage (continuous_subtype_val.comp continuous_subtype_val)
    rw [open_set.interior_eq]
    exact ⟨0, 0, map_zero integralEmbedding⟩

/-- Additive Haar measure on `awayS S`, normalised by the integral points. -/
def awayMeasure (S : Finset FinitePlace) : Measure (awayS S) :=
  Measure.addHaarMeasure (awayUnitCompact S)

instance awayMeasure_haar (S : Finset FinitePlace) : (awayMeasure S).IsAddHaarMeasure :=
  inferInstanceAs ((Measure.addHaarMeasure (awayUnitCompact S)).IsAddHaarMeasure)

instance awayMeasure_sigmaFinite (S : Finset FinitePlace) : SigmaFinite (awayMeasure S) :=
  inferInstanceAs (SigmaFinite (Measure.addHaarMeasure (awayUnitCompact S)))

theorem awayMeasure_normalized (S : Finset FinitePlace) :
    awayMeasure S ((fun value : awayS S => value.val.val) ⁻¹' Set.range integralEmbedding) = 1 :=
  Measure.addHaarMeasure_self

/-- A Haar measure pushed forward by a continuous additive equivalence whose preimage of a
compact `K` has measure one is the normalised Haar measure of `K`. -/
theorem map_eq_addHaarMeasure_of_preimage {G H : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [LocallyCompactSpace H]
    [MeasurableSpace H] [BorelSpace H] [T2Space H] [SecondCountableTopology H]
    (f : G ≃ₜ+ H) (μ : Measure G) [μ.IsAddHaarMeasure] (K : PositiveCompacts H)
    (hK : MeasurableSet (K : Set H)) (h : μ (f ⁻¹' (K : Set H)) = 1) :
    Measure.map f μ = Measure.addHaarMeasure K := by
  have unique := Measure.addHaarMeasure_unique (Measure.map f μ) K
  have hfm : Measurable (⇑f : G → H) := f.continuous.measurable
  have value : Measure.map f μ (K : Set H) = 1 := by
    rw [Measure.map_apply hfm hK, h]
  rw [value, one_smul] at unique
  exact unique


theorem awayStepSymm_val (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace)
    (hS : q ∉ S) (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q) (pr : q.adicCompletion ℚ × awayS T) :
    ((awayStepSplit q hq S T hS hT).symm pr).val.val =
      finiteAtPlaceScalar q pr.1 + pr.2.val.val := rfl

theorem awayStep_integral_iff (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace)
    (hS : q ∉ S) (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q) (pr : q.adicCompletion ℚ × awayS T) :
    ((awayStepSplit q hq S T hS hT).symm pr).val.val ∈ Set.range integralEmbedding ↔
      pr.1 ∈ q.adicCompletionIntegers ℚ ∧ pr.2.val.val ∈ Set.range integralEmbedding := by
  rw [awayStepSymm_val]
  constructor
  · rintro ⟨integer, equality⟩
    have away_zero : finiteEvaluation q pr.2.val.val = 0 :=
      (mem_awayS.mp pr.2.property) q ((hT q).mpr (Or.inr rfl))
    have local_eq : (integer q).val = pr.1 := by
      have equal := congrArg (finiteEvaluation q) equality
      rwa [integralEmbedding_at, map_add, finiteAtPlaceScalar_same, away_zero, add_zero] at equal
    have local_integral : pr.1 ∈ q.adicCompletionIntegers ℚ := local_eq ▸ (integer q).property
    refine ⟨local_integral, ?_⟩
    have embedded := finiteAtPlaceScalar_integral q ⟨pr.1, local_integral⟩
    have original : finiteAtPlaceScalar q pr.1 + pr.2.val.val ∈ integralEmbedding.range := ⟨integer, equality⟩
    have difference := integralEmbedding.range.sub_mem original embedded
    simp only [add_sub_cancel_left] at difference
    exact difference
  · rintro ⟨local_integral, away_integral⟩
    exact integralEmbedding.range.add_mem (finiteAtPlaceScalar_integral q ⟨pr.1, local_integral⟩) away_integral

theorem awayStep_symm_measurePreserving (q : FinitePlace) (hq : q ≠ placeThree) (S T : Finset FinitePlace)
    (hS : q ∉ S) (hT : ∀ p, p ∈ T ↔ p ∈ S ∨ p = q) :
    MeasurePreserving (awayStepSplit q hq S T hS hT).symm
      ((finiteCompletionMeasure q).prod (awayMeasure T)) (awayMeasure S) := by
  have measurable : Measurable ((awayStepSplit q hq S T hS hT).symm) :=
    (awayStepSplit q hq S T hS hT).symm.continuous.measurable
  have hK : MeasurableSet ((awayUnitCompact S : Set (awayS S))) :=
    (integralLattice_isOpen.preimage (continuous_subtype_val.comp continuous_subtype_val)).measurableSet
  have preimage : (awayStepSplit q hq S T hS hT).symm ⁻¹' (awayUnitCompact S : Set (awayS S)) =
      ((q.adicCompletionIntegers ℚ : Set (q.adicCompletion ℚ)) ×ˢ
        ((fun value : awayS T => value.val.val) ⁻¹' Set.range integralEmbedding)) := by
    ext pr
    exact awayStep_integral_iff q hq S T hS hT pr
  have normalized : ((finiteCompletionMeasure q).prod (awayMeasure T))
      ((awayStepSplit q hq S T hS hT).symm ⁻¹' (awayUnitCompact S : Set (awayS S))) = 1 := by
    rw [preimage, Measure.prod_prod, finiteCompletionMeasure_normalized, awayMeasure_normalized, mul_one]
  exact ⟨measurable, map_eq_addHaarMeasure_of_preimage (awayStepSplit q hq S T hS hT).symm
    ((finiteCompletionMeasure q).prod (awayMeasure T)) (awayUnitCompact S) hK normalized⟩

end TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
