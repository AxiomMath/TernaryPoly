module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.SumPoisson

@[expose] public section


open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactCosetExpansion

variable {Group : Type*} [AddCommGroup Group] [TopologicalSpace Group] [IsTopologicalAddGroup Group]

omit [TopologicalSpace Group] [IsTopologicalAddGroup Group] in
theorem same_class (subgroup : AddSubgroup Group) (function : Group → ℂ)
    (invariant : ∀ shift ∈ subgroup, ∀ value, function (shift + value) = function value)
    (first second : Group) (equality : (QuotientAddGroup.mk first : Group ⧸ subgroup) = QuotientAddGroup.mk second) :
    function first = function second := by
  have membership := QuotientAddGroup.eq_iff_sub_mem.mp equality
  have result := invariant (first - second) membership second
  simpa only [sub_add_cancel] using result

theorem expansion (subgroup : AddSubgroup Group) (openness : IsOpen (subgroup : Set Group))
    (function : Group → ℂ) (compactSupport : HasCompactSupport function)
    (invariant : ∀ shift ∈ subgroup, ∀ value, function (shift + value) = function value) :
    ∃ indices : Finset (Group ⧸ subgroup), ∀ value : Group,
      function value = ∑ coset ∈ indices,
        if (QuotientAddGroup.mk value : Group ⧸ subgroup) = coset then function coset.out else 0 := by
  let : DiscreteTopology (Group ⧸ subgroup) := QuotientAddGroup.discreteTopology openness
  let projection : Group → Group ⧸ subgroup := QuotientAddGroup.mk
  have finiteClasses : (projection '' tsupport function).Finite :=
    (compactSupport.image QuotientAddGroup.continuous_mk).finite_of_discrete
  let indices := finiteClasses.toFinset
  have outsideZero (coset : Group ⧸ subgroup) (outside : coset ∉ indices) : function coset.out = 0 := by
    by_contra nonzero
    apply outside
    apply finiteClasses.mem_toFinset.mpr
    exact ⟨coset.out, subset_closure nonzero, Quotient.out_eq' coset⟩
  refine ⟨indices, fun value => ?_⟩
  have representative : function (projection value).out = function value :=
    same_class subgroup function invariant _ _ (Quotient.out_eq' _)
  rw [Finset.sum_eq_single (projection value)]
  · simpa only [projection, ite_true] using representative.symm
  · intro other _ different
    exact ite_eq_right (Ne.symm different)
  · intro outside
    simpa only [projection, ite_true] using outsideZero (projection value) outside

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactCosetExpansion
