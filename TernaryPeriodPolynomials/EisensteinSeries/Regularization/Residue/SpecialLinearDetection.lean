module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.PrincipalQuotient

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem real_matrix_scalar_det_one (matrix : RealGL3) :
    ∃ scalar : ℝˣ, (GeneralLinearGroup.scalar (Fin 3) scalar * matrix).val.det = 1 := by
  obtain ⟨scalar, _, determinant⟩ := real_matrix_positive_scalar_unit_det matrix
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp determinant with positive | negative
  · exact ⟨scalar, positive⟩
  · refine ⟨-scalar, ?_⟩
    have sign : (GeneralLinearGroup.scalar (Fin 3) (-scalar) * matrix).val.det =
        -(GeneralLinearGroup.scalar (Fin 3) scalar * matrix).val.det := by
      change (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) (-scalar) * matrix)).val =
        -(GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) scalar * matrix)).val
      simp [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_mul,
        Units.val_pow_eq_pow_val, Units.val_neg]
      ring
    rw [sign, negative]
    norm_num

theorem normalizedBoundaryResidue_zero_of_specialLinear_slices
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (zero : ∀ integral : GL3 IntegralAdeles, ∀ matrix : SpecialLinearGroup (Fin 3) ℝ,
      normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix) = 0)
    (matrix : AdelicGL) : normalizedBoundaryResidue degree continuation matrix = 0 := by
  obtain ⟨rational, realMatrix, integral, decomposition⟩ := adelic_rational_real_integral matrix
  rw [decomposition, mul_assoc, normalizedBoundaryResidue_rational_invariant flat continuation_spec]
  obtain ⟨scalar, determinant⟩ := real_matrix_scalar_det_one realMatrix
  let special : SpecialLinearGroup (Fin 3) ℝ :=
    ⟨(GeneralLinearGroup.scalar (Fin 3) scalar * realMatrix).val, determinant⟩
  have special_coe : SpecialLinearGroup.toGL special = GeneralLinearGroup.scalar (Fin 3) scalar * realMatrix :=
    Units.ext rfl
  have identity : realSpecialIntegralSlice integral special =
      GeneralLinearGroup.scalar (Fin 3) (realAdeleUnit scalar) *
        (atInfinity realMatrix * atFinite (GeneralLinearGroup.map integralEmbedding integral)) := by
    rw [realSpecialIntegralSlice, special_coe, atInfinity_mul, ternary_atInfinity_scalar, mul_assoc]
  have norm_identity := normalizedBoundaryResidue_central_norm flat continuation_spec (realAdeleUnit scalar)
    (atInfinity realMatrix * atFinite (GeneralLinearGroup.map integralEmbedding integral))
  rw [← identity, zero integral special, norm_zero] at norm_identity
  exact norm_eq_zero.mp norm_identity.symm

theorem normalizedBoundaryResidue_zero_of_principalQuotient_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (zero : ∀ integral : GL3 IntegralAdeles,
      normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral = 0)
    (matrix : AdelicGL) : normalizedBoundaryResidue degree continuation matrix = 0 := by
  apply normalizedBoundaryResidue_zero_of_specialLinear_slices flat continuation_spec _ matrix
  intro integral special
  have equality := congrFun (zero integral) (Quotient.mk'' special)
  exact equality

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
