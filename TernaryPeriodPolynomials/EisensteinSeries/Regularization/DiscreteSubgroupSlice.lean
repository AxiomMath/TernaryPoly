module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.MeasurableGroupDomain

@[expose] public section


namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem discrete_subgroup_measurable_slice_domain
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LindelofSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (subgroup : Subgroup G) [DiscreteTopology subgroup] [Countable subgroup]
    (slice : Set G) (slice_measurable : MeasurableSet slice)
    (invariant : ∀ element : subgroup, ∀ point ∈ slice, element.val * point ∈ slice) :
    ∃ domain : Set G, MeasurableSet domain ∧ domain ⊆ slice ∧
      ∀ point ∈ slice, ∃! element : subgroup, element.val * point ∈ domain := by
  obtain ⟨cover, open_cover, covers, separated⟩ := discrete_subgroup_countable_separated_cover subgroup
  obtain ⟨domain, measurable, unique⟩ := subgroup_measurable_domain_of_cover subgroup cover
    (fun index => (open_cover index).measurableSet) covers separated
  refine ⟨domain ∩ slice, measurable.inter slice_measurable, Set.inter_subset_right, ?_⟩
  intro point member
  obtain ⟨element, selected, unique_element⟩ := unique point
  exact ⟨element, ⟨selected, invariant element point member⟩,
    fun other other_selected => unique_element other other_selected.1⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
