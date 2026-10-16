module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearPlaneLevi
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.SpecialLinear
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.DiscreteSubgroupSlice

@[expose] public section


open Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def principalRealPlaneLevi : Subgroup (SpecialLinearGroup (Fin 3) ℝ) :=
  principalRealSpecialLinear ⊓ (specialLinearPlaneLevi (R := ℝ)).range

theorem principalRealPlaneLevi_le_principal : principalRealPlaneLevi ≤ principalRealSpecialLinear :=
  inf_le_left

instance principalRealPlaneLevi_countable : Countable principalRealPlaneLevi :=
  Function.Injective.countable (Subgroup.inclusion_injective principalRealPlaneLevi_le_principal)

instance principalRealPlaneLevi_discrete : DiscreteTopology principalRealPlaneLevi := by
  have embedding : Topology.IsEmbedding (Subgroup.inclusion principalRealPlaneLevi_le_principal) :=
    (Topology.IsEmbedding.of_comp_iff (f := Subgroup.inclusion principalRealPlaneLevi_le_principal)
      (g := (Subtype.val : principalRealSpecialLinear → SpecialLinearGroup (Fin 3) ℝ))
      Topology.IsEmbedding.subtypeVal).mp Topology.IsEmbedding.subtypeVal
  exact embedding.discreteTopology

theorem principalRealPlaneLevi_slice_invariant (element : principalRealPlaneLevi)
    (matrix : SpecialLinearGroup (Fin 3) ℝ) (member : matrix ∈ realPlaneNormalSet) :
    element.val * matrix ∈ realPlaneNormalSet := by
  obtain ⟨binary, represents⟩ := element.property.2
  rw [← represents]
  exact realPlaneNormalSet_levi_invariant binary matrix member

theorem principalRealPlaneLevi_slice_domain_exists :
    ∃ domain : Set (SpecialLinearGroup (Fin 3) ℝ), MeasurableSet domain ∧
      domain ⊆ realPlaneNormalSet ∧ ∀ point ∈ realPlaneNormalSet,
        ∃! element : principalRealPlaneLevi, element.val * point ∈ domain :=
  discrete_subgroup_measurable_slice_domain principalRealPlaneLevi realPlaneNormalSet
    realPlaneNormalSet_closed.measurableSet principalRealPlaneLevi_slice_invariant

noncomputable def principalPlaneSliceDomain : Set (SpecialLinearGroup (Fin 3) ℝ) :=
  Classical.choose principalRealPlaneLevi_slice_domain_exists

theorem principalPlaneSliceDomain_measurable : MeasurableSet principalPlaneSliceDomain :=
  (Classical.choose_spec principalRealPlaneLevi_slice_domain_exists).1

theorem principalPlaneSliceDomain_subset : principalPlaneSliceDomain ⊆ realPlaneNormalSet :=
  (Classical.choose_spec principalRealPlaneLevi_slice_domain_exists).2.1

theorem principalPlaneSliceDomain_unique (point : SpecialLinearGroup (Fin 3) ℝ)
    (member : point ∈ realPlaneNormalSet) :
    ∃! element : principalRealPlaneLevi, element.val * point ∈ principalPlaneSliceDomain :=
  (Classical.choose_spec principalRealPlaneLevi_slice_domain_exists).2.2 point member

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
