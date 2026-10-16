module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.CasimirGraphBlocks

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem cohomological_casimir_bounded_weak_extension {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    ∃ operator : cusp.H →L[ℂ] cusp.H,
      (∀ vector : cusp.H, ∀ test : cusp.smooth,
        inner ℂ (operator vector) test.val = inner ℂ vector (cuspCasimirOperator cusp test).val) ∧
      ∀ matrix, Commute operator (cuspUnitaryAction cusp matrix).toContinuousLinearMap := by
  obtain ⟨scalar, scalar_ne, first_scalar⟩ := cuspCasimirGraphFirst_scalar cohomological
  have complex_ne : (scalar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scalar_ne
  let operator : cusp.H →L[ℂ] cusp.H := (scalar : ℂ)⁻¹ • cuspCasimirGraphSecond cusp
  refine ⟨operator, ?_, fun matrix => (cuspCasimirGraphSecond_commuting cusp matrix).smul_left _⟩
  intro vector test
  let pair := (cuspWeakCasimirGraph cusp).starProjection
    (cuspPairInclusion cusp ((scalar : ℂ)⁻¹ • vector))
  have first : pair.ofLp.1 = vector := by
    change cuspCasimirGraphFirst cusp ((scalar : ℂ)⁻¹ • vector) = vector
    rw [first_scalar]
    change (scalar : ℂ) • ((scalar : ℂ)⁻¹ • vector) = vector
    rw [smul_smul, mul_inv_cancel₀ complex_ne, one_smul]
  have second : pair.ofLp.2 = operator vector := by
    change cuspCasimirGraphSecond cusp ((scalar : ℂ)⁻¹ • vector) =
      (scalar : ℂ)⁻¹ • cuspCasimirGraphSecond cusp vector
    exact map_smul _ _ _
  have relation := (cuspWeakCasimirGraph cusp).starProjection_apply_mem
    (cuspPairInclusion cusp ((scalar : ℂ)⁻¹ • vector))
  change pair ∈ cuspWeakCasimirGraph cusp at relation
  have equality := relation test
  rw [first, second] at equality
  exact equality

theorem cohomological_casimir_extension_eq {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (operator : cusp.H →L[ℂ] cusp.H)
    (weak_extension : ∀ vector : cusp.H, ∀ test : cusp.smooth,
      inner ℂ (operator vector) test.val = inner ℂ vector (cuspCasimirOperator cusp test).val)
    (vector : cusp.smooth) : operator vector.val = (cuspCasimirOperator cusp vector).val := by
  apply sub_eq_zero.mp
  apply cohomological_inner_ext cohomological
  intro test
  rw [inner_sub_left, weak_extension, cuspCasimirOperator_symmetric, sub_self]

theorem cohomological_casimir_extension_selfAdjoint {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (operator : cusp.H →L[ℂ] cusp.H)
    (weak_extension : ∀ vector : cusp.H, ∀ test : cusp.smooth,
      inner ℂ (operator vector) test.val = inner ℂ vector (cuspCasimirOperator cusp test).val) :
    IsSelfAdjoint operator := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro vector test
  have closed : IsClosed {test : cusp.H | inner ℂ (operator vector) test = inner ℂ vector (operator test)} :=
    isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner operator.continuous)
  have subset : (cusp.smooth : Set cusp.H) ⊆
      {test : cusp.H | inner ℂ (operator vector) test = inner ℂ vector (operator test)} := by
    intro test member
    change inner ℂ (operator vector) test = inner ℂ vector (operator test)
    rw [cohomological_casimir_extension_eq cohomological operator weak_extension ⟨test, member⟩]
    exact weak_extension vector ⟨test, member⟩
  exact closure_minimal subset closed ((cohomological_smooth_dense cohomological) test)

theorem cohomological_casimir_scalar {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    ∃ scalar : ℝ, cuspCasimirOperator cusp = (scalar : ℂ) • (1 : Module.End ℂ cusp.smooth) := by
  obtain ⟨operator, weak_extension, commuting⟩ := cohomological_casimir_bounded_weak_extension cohomological
  obtain ⟨scalar, scalar_action⟩ := cusp_commuting_selfAdjoint_scalar cusp operator
    (cohomological_casimir_extension_selfAdjoint cohomological operator weak_extension) commuting
  refine ⟨scalar, ?_⟩
  apply LinearMap.ext
  intro vector
  apply Subtype.ext
  change (cuspCasimirOperator cusp vector).val = (scalar : ℂ) • vector.val
  rw [← cohomological_casimir_extension_eq cohomological operator weak_extension, scalar_action]
  rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
