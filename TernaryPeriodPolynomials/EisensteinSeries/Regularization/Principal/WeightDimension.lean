module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.WeightOperators

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cohomological_principal_bottom_eq_lowest
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree) :
    cuspPrincipalWeightSubmodule cusp (degree + 3) = cuspPrincipalLowestSubmodule cusp (degree + 3) := by
  apply Submodule.ext
  intro vector
  constructor
  · intro member
    refine ⟨member.1, ?_, ?_⟩
    · simpa only [Nat.cast_add, Int.cast_add, Nat.cast_ofNat, Int.cast_ofNat, Int.cast_natCast] using member.2
    · apply cohomological_bottom_lowering_zero cohomological
      simpa only [Int.cast_add, Int.cast_ofNat, Int.cast_natCast] using member.2
  · intro member
    refine ⟨member.1, ?_⟩
    simpa only [Nat.cast_add, Int.cast_add, Nat.cast_ofNat, Int.cast_ofNat, Int.cast_natCast] using member.2.1

theorem cohomological_principal_naturalWeight_finiteDimensional
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℕ) : FiniteDimensional ℂ (cuspPrincipalWeightSubmodule cusp weight) := by
  induction weight using Nat.strong_induction_on with
  | h weight induction =>
    rcases lt_trichotomy weight (degree + 3) with below | bottom | above
    · have zero : cuspPrincipalWeightSubmodule cusp (weight : ℤ) = ⊥ := by
        apply (Submodule.eq_bot_iff _).mpr
        intro vector member
        by_contra nonzero
        obtain ⟨step, spectrum⟩ :=
          cohomological_integer_weight_spectrum cohomological weight vector nonzero member.2
        simp only [Int.natAbs_natCast] at spectrum
        omega
      rw [zero]
      infer_instance
    · subst weight
      rw [Nat.cast_add, Nat.cast_ofNat, cohomological_principal_bottom_eq_lowest cohomological]
      exact cuspPrincipalLowest_finiteDimensional cohomological (degree + 3) (by omega)
    · have smaller : weight - 2 < weight := by omega
      have cast : ((weight - 2 : ℕ) : ℤ) = (weight : ℤ) - 2 := by omega
      let : FiniteDimensional ℂ (cuspPrincipalWeightSubmodule cusp ((weight : ℤ) - 2)) := by
        rw [← cast]
        exact induction (weight - 2) smaller
      exact FiniteDimensional.of_injective (cuspPrincipalWeightLowering cusp weight)
        (cohomological_principal_lowering_injective cohomological weight (by exact_mod_cast above))

theorem cohomological_principal_weight_finiteDimensional
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℤ) : FiniteDimensional ℂ (cuspPrincipalWeightSubmodule cusp weight) := by
  by_cases nonnegative : 0 ≤ weight
  · lift weight to ℕ using nonnegative
    exact cohomological_principal_naturalWeight_finiteDimensional cohomological weight
  · have positive : 0 ≤ -weight := by omega
    let : FiniteDimensional ℂ (cuspPrincipalWeightSubmodule cusp (-weight)) := by
      have cast : ((-weight).toNat : ℤ) = -weight := Int.toNat_of_nonneg positive
      rw [← cast]
      exact cohomological_principal_naturalWeight_finiteDimensional cohomological _
    exact FiniteDimensional.of_injective (cuspPrincipalWeightReflection cusp weight)
      (cuspPrincipalWeightReflection_injective cusp weight)

theorem cohomological_principal_weight_scalar_bound
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℤ) : ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ vector : cuspPrincipalWeightSubmodule cusp weight,
        ‖cuspBoundedRealization cusp vector.val‖ ≤ constant * ‖vector.val.val‖ := by
  let : FiniteDimensional ℂ (cuspPrincipalWeightSubmodule cusp weight) :=
    cohomological_principal_weight_finiteDimensional cohomological weight
  let realization := (cuspBoundedRealization cusp).comp (cuspPrincipalWeightSubmodule cusp weight).subtype
  let continuousRealization := realization.toContinuousLinearMap
  exact ⟨‖continuousRealization‖, continuousRealization.opNorm_nonneg,
    fun vector => continuousRealization.le_opNorm vector⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
