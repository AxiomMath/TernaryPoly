module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.SubgroupFundamentalDomain

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SliceFundamentalDomain

variable {ActingGroup Space : Type*} [Group ActingGroup] [MulAction ActingGroup Space]

theorem unique (subgroup : Subgroup ActingGroup) (original slice : Set Space)
    (originalUnique : ∀ point, ∃! element : subgroup, element • point ∈ original)
    (sliceExists : ∀ point, ∃ element : ActingGroup, element • point ∈ slice)
    (sliceReturn : ∀ (point : Space), point ∈ slice → ∀ element : ActingGroup, element • point ∈ slice ↔ element ∈ subgroup)
    (point : Space) : ∃! element : ActingGroup, element • point ∈ original ∩ slice := by
  obtain ⟨first, firstMem⟩ := sliceExists point
  obtain ⟨second, secondMem, _⟩ := originalUnique (first • point)
  have secondSlice : second.val • (first • point) ∈ slice :=
    (sliceReturn _ firstMem second.val).mpr second.property
  let chosen : ActingGroup := second.val * first
  have chosenMem : chosen • point ∈ original ∩ slice := by
    change (second.val * first) • point ∈ original ∩ slice
    rw [mul_smul]
    exact ⟨secondMem, secondSlice⟩
  refine ⟨chosen, chosenMem, ?_⟩
  intro other otherMem
  have ratioSlice : (other * chosen⁻¹) • (chosen • point) ∈ slice := by
    simpa only [mul_smul, inv_smul_smul] using otherMem.2
  let ratio : subgroup := ⟨other * chosen⁻¹, (sliceReturn _ chosenMem.2 _).mp ratioSlice⟩
  obtain ⟨representative, _, uniqueness⟩ := originalUnique (chosen • point)
  have ratioMem : ratio • (chosen • point) ∈ original := by
    change (other * chosen⁻¹) • (chosen • point) ∈ original
    simpa only [mul_smul, inv_smul_smul] using otherMem.1
  have oneMem : (1 : subgroup) • (chosen • point) ∈ original := by
    simpa only [one_smul] using chosenMem.1
  have equality : ratio = 1 := (uniqueness ratio ratioMem).trans (uniqueness 1 oneMem).symm
  have ratioOne : other * chosen⁻¹ = 1 := congrArg Subtype.val equality
  exact mul_inv_eq_one.mp ratioOne

theorem fundamental [MeasurableSpace Space] (subgroup : Subgroup ActingGroup) (original slice : Set Space)
    (originalMeasurable : MeasurableSet original) (sliceMeasurable : MeasurableSet slice)
    (originalUnique : ∀ point, ∃! element : subgroup, element • point ∈ original)
    (sliceExists : ∀ point, ∃ element : ActingGroup, element • point ∈ slice)
    (sliceReturn : ∀ (point : Space), point ∈ slice → ∀ element : ActingGroup, element • point ∈ slice ↔ element ∈ subgroup)
    (measure : Measure Space) : IsFundamentalDomain ActingGroup (original ∩ slice) measure :=
  IsFundamentalDomain.mk' (originalMeasurable.inter sliceMeasurable).nullMeasurableSet
    (unique subgroup original slice originalUnique sliceExists sliceReturn)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SliceFundamentalDomain
