module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.InfiniteOrbitIntegrand

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem summable_tsum_option {Index : Type*} (function : Option Index → ℂ)
    (summable : Summable function) :
    (∑' index, function index) = function none + ∑' index, function (some index) := by
  let equivalence : Option Index ≃ Index ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit Index
  have sum_summable : Summable (function ∘ equivalence.symm) :=
    equivalence.symm.summable_iff.mpr summable
  have left_summable := sum_summable.comp_injective Sum.inl_injective
  have right_summable := sum_summable.comp_injective Sum.inr_injective
  calc
    _ = ∑' index : Index ⊕ PUnit.{1}, function (equivalence.symm index) :=
      (equivalence.symm.tsum_eq function).symm
    _ = (∑' index : Index, function (some index)) + function none := by
      simpa [equivalence] using left_summable.tsum_sum right_summable
    _ = _ := add_comm _ _

theorem planeFlag_tsum (function : Flags .plane → ℂ) (summable : Summable function) :
    (∑' flag, function flag) = function (planeFlag none) +
      (∑' offset : ℚ, function (planeFlag (some (none, offset)))) +
      ∑' slope : ℚ, ∑' offset : ℚ, function (planeFlag (some (some slope, offset))) := by
  have indexed_summable : Summable (fun index => function (planeFlag index)) :=
    planeFlagEquiv.summable_iff.mpr summable
  have open_summable : Summable (fun index : Option ℚ × ℚ => function (planeFlag (some index))) :=
    indexed_summable.comp_injective (Option.some_injective _)
  calc
    _ = ∑' index, function (planeFlag index) := (planeFlagEquiv.tsum_eq function).symm
    _ = function (planeFlag none) +
        ∑' index : Option ℚ × ℚ, function (planeFlag (some index)) :=
      summable_tsum_option _ indexed_summable
    _ = function (planeFlag none) +
        ∑' slope : Option ℚ, ∑' offset : ℚ, function (planeFlag (some (slope, offset))) := by
      rw [open_summable.tsum_prod]
    _ = function (planeFlag none) +
        ((∑' offset : ℚ, function (planeFlag (some (none, offset)))) +
          ∑' slope : ℚ, ∑' offset : ℚ, function (planeFlag (some (some slope, offset)))) := by
      rw [summable_tsum_option _ open_summable.prod]
    _ = _ := (add_assoc _ _ _).symm

theorem eisenstein_sum_flag_coordinates
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter sumValue : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL)
    (sum_spec : HasSum (eisensteinSummand family parameter groupElement) sumValue) :
    sumValue = family parameter groupElement +
      (∑' offset : ℚ, eisensteinSummand family parameter groupElement (planeFlag (some (none, offset)))) +
      ∑' slope : ℚ, ∑' offset : ℚ,
        eisensteinSummand family parameter groupElement (planeFlag (some (some slope, offset))) := by
  have closed_term : eisensteinSummand family parameter groupElement (planeFlag none) =
      family parameter groupElement := by
    rw [planeFlag, planeFlagMatrix, eisensteinSummand_of_representative induced]
    simp
  rw [← sum_spec.tsum_eq, planeFlag_tsum _ sum_spec.summable, closed_term]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
