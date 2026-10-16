module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REVector
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad1
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RESets
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.ThreeMeasure
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.LocalThreeEntry.Helpers

@[expose] public section


/-!
# R-e: The small `3`-adic region and its measure

`badRegion` (`3`-adic coordinates in `3ℤ₃`), `entryRegion_bad_measure` (`1/9`) and the base integral `entryBase_bad`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

attribute [local instance] reDecEq

/-- The region `‖v₁‖₃ < 1`, `‖v₂‖₃ < 1`: both `3`-adic coordinates lie in `3ℤ₃`. -/
def badRegion : Set (FiniteAdeles × FiniteAdeles) :=
  {v | ‖finiteThree v.1‖ < 1 ∧ ‖finiteThree v.2‖ < 1}

theorem finiteThree_norm_continuous : Continuous (fun v : FiniteAdeles => ‖finiteThree v‖) :=
  continuous_norm.comp finiteThree_continuous

theorem badRegion_measurable : MeasurableSet badRegion := by
  have first : IsOpen {v : FiniteAdeles × FiniteAdeles | ‖finiteThree v.1‖ < 1} :=
    isOpen_lt (finiteThree_norm_continuous.comp continuous_fst) continuous_const
  have second : IsOpen {v : FiniteAdeles × FiniteAdeles | ‖finiteThree v.2‖ < 1} :=
    isOpen_lt (finiteThree_norm_continuous.comp continuous_snd) continuous_const
  exact (first.inter second).measurableSet

theorem threeStable_badRegion : ThreeStable badRegion := by
  refine ⟨badRegion_measurable, ?_⟩
  intro v w w1 w2
  simp only [badRegion, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, map_add, w1, w2, add_zero]

/-- Integrality at three from a small `3`-adic norm. -/
theorem integral_at_three_of_norm_le {w : FiniteAdeles} (small : ‖finiteThree w‖ ≤ 1) :
    finiteEvaluation placeThree w ∈ placeThree.adicCompletionIntegers ℚ := by
  let integer : ℤ_[3] := ⟨finiteThree w, small⟩
  have h := threeIntegral_coe (threeIntegralEquiv.symm integer)
  rw [RingEquiv.apply_symm_apply] at h
  have : threeCompletionEquiv ((threeIntegralEquiv.symm integer).val) = threeCompletionEquiv (finiteEvaluation placeThree w) := by
    rw [← h]
    rfl
  have equal := threeCompletionEquiv.injective this
  rw [← equal]
  exact (threeIntegralEquiv.symm integer).property

/-- The one-coordinate region `‖w‖₃ < 1`, integral away from three. -/
def badCoordinate : Set FiniteAdeles :=
  {w | ‖finiteThree w‖ < 1 ∧ w ∈ finiteIntegralOutside (insert placeThree ∅)}

theorem entryRegion_bad_empty : entryRegion badRegion ∅ = badCoordinate ×ˢ badCoordinate := by
  ext v
  simp only [entryRegion, badRegion, badCoordinate, Set.mem_ofPred_eq, Set.mem_prod]
  tauto

theorem finiteAwayThree_val (w : FiniteAdeles) :
    (finiteAwayThree w).val = w - finiteAtThreeScalar (finiteThree w) := rfl

theorem badCoordinate_eq : badCoordinate = finiteThreeSplit ⁻¹'
    (TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers.smallBall ×ˢ
      (Subtype.val ⁻¹' Set.range integralEmbedding : Set FiniteAwayThree)) := by
  ext w
  simp only [badCoordinate, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod]
  have split : (finiteThreeSplit w).1 = finiteThree w := rfl
  have away : (finiteThreeSplit w).2 = finiteAwayThree w := rfl
  rw [split, away]
  change ‖finiteThree w‖ < 1 ∧ w ∈ finiteIntegralOutside (insert placeThree ∅) ↔
    ‖finiteThree w‖ < 1 ∧ (finiteAwayThree w).val ∈ Set.range integralEmbedding
  rw [← finiteIntegralOutside_empty]
  refine and_congr_right fun _ => ?_
  constructor
  · intro integral place _
    rw [finiteAwayThree_val]
    by_cases same : place = placeThree
    · subst same
      have zero := finiteAwayThree_evaluation_zero (finiteAwayThree w)
      rw [finiteAwayThree_val] at zero
      rw [zero]
      exact zero_mem _
    · rw [map_sub, finiteAtThreeScalar_away _ _ same, sub_zero]
      exact integral place (by simp [same])
  · intro integral place outside
    have same : place ≠ placeThree := by
      intro h
      exact outside (by simp [h])
    have member := integral place (Finset.notMem_empty place)
    rw [finiteAwayThree_val, map_sub, finiteAtThreeScalar_away _ _ same, sub_zero] at member
    exact member

theorem smallBall_measurable :
    MeasurableSet TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers.smallBall :=
  (isOpen_lt continuous_norm continuous_const).measurableSet

theorem badCoordinate_measure : finiteMeasure badCoordinate = (1 / 3 : ℝ≥0∞) := by
  have := normalizedLocalThreeMeasure_haar
  have measurable : MeasurableSet
      (TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers.smallBall ×ˢ
        (Subtype.val ⁻¹' Set.range integralEmbedding : Set FiniteAwayThree)) :=
    smallBall_measurable.prod ((integralLattice_isOpen.preimage continuous_subtype_val).measurableSet)
  rw [badCoordinate_eq, finiteThreeSplit_measurePreserving.measure_preimage measurable.nullMeasurableSet,
    Measure.prod_prod, finiteAwayThreeMeasure_normalized, mul_one]
  exact TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers.smallBall_measure
    normalizedLocalThreeMeasure normalizedLocalThreeMeasure_normalized

theorem badCoordinate_measurable : MeasurableSet badCoordinate := by
  rw [badCoordinate_eq]
  have := normalizedLocalThreeMeasure_haar
  exact (smallBall_measurable.prod ((integralLattice_isOpen.preimage continuous_subtype_val).measurableSet)).preimage
    finiteThreeSplit.toHomeomorph.toMeasurableEquiv.measurable

theorem entryRegion_bad_measure :
    (finiteMeasure.prod finiteMeasure) (entryRegion badRegion ∅) = (1 / 9 : ℝ≥0∞) := by
  rw [entryRegion_bad_empty, Measure.prod_prod, badCoordinate_measure]
  rw [one_div, one_div, ← ENNReal.mul_inv (by left; norm_num) (by right; norm_num)]
  norm_num

theorem entryIntegrand_badRegion (cusp : CuspidalRepresentation) (vector : cusp.smooth) (m : BinaryFiniteGL)
    (e : ℂ) (v : FiniteAdeles × FiniteAdeles) (member : v ∈ entryRegion badRegion ∅) :
    entryIntegrand cusp vector m e v = entryBaseValue cusp vector m e := by
  obtain ⟨⟨small₁, small₂⟩, outside₁, outside₂⟩ := member
  have h₁ : v.1 ∈ finiteIntegralOutside ∅ := by
    intro place _
    by_cases same : place = placeThree
    · subst same
      exact integral_at_three_of_norm_le small₁.le
    · exact outside₁ place (by simp [same])
  have h₂ : v.2 ∈ finiteIntegralOutside ∅ := by
    intro place _
    by_cases same : place = placeThree
    · subst same
      exact integral_at_three_of_norm_le small₂.le
    · exact outside₂ place (by simp [same])
  exact entryIntegrand_integral cusp vector m e v h₁ h₂

theorem entryBase_bad (cusp : CuspidalRepresentation) (vector : cusp.smooth) (m : BinaryFiniteGL) (e : ℂ) :
    (∫ v in entryRegion badRegion ∅, entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure)) =
      (1 / 9 : ℂ) * entryBaseValue cusp vector m e := by
  rw [setIntegral_congr_fun (entryRegion_measurable threeStable_badRegion ∅)
    (fun v member => entryIntegrand_badRegion cusp vector m e v member), setIntegral_const, Measure.real,
    entryRegion_bad_measure]
  simp [Complex.real_smul]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
