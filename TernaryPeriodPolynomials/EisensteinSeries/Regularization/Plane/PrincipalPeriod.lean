module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.FiniteCompatibility

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem integral_principal_finite_conjugate (principal integral : GL3 IntegralAdeles)
    (reduction : GeneralLinearGroup.map integralReduction principal = 1) :
    (GeneralLinearGroup.map integralEmbedding integral)⁻¹ *
      GeneralLinearGroup.map integralEmbedding principal *
      GeneralLinearGroup.map integralEmbedding integral ∈ finiteLevel := by
  refine ⟨integral⁻¹ * principal * integral, ?_, ?_⟩
  · change GeneralLinearGroup.map integralReduction (integral⁻¹ * principal * integral) ∈
      GeneralEisenstein.rowStabilizer
    simp only [map_mul, map_inv, reduction, mul_one, inv_mul_cancel, Subgroup.one_mem]
  · simp only [map_mul, map_inv]

theorem planeUnipotent_three_reduction (first second : IntegralAdeles) :
    GeneralLinearGroup.map integralReduction (planeUnipotent (3 * first) (3 * second)) = 1 := by
  rw [map_planeUnipotent]
  have first_zero : integralReduction (3 * first) = 0 := by
    rw [map_mul, map_ofNat, show (3 : ZMod 3) = 0 from by decide, zero_mul]
  have second_zero : integralReduction (3 * second) = 0 := by
    rw [map_mul, map_ofNat, show (3 : ZMod 3) = 0 from by decide, zero_mul]
  rw [first_zero, second_zero]
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;> norm_num [planeUnipotent]

theorem atFinite_planeUnipotent (first second : FiniteAdeles) :
    atFinite (planeUnipotent first second) = planeUnipotent (0, first) (0, second) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;> simp [atFinite, combineGL, pairMatrix, planeUnipotent]

theorem planeUnipotent_adelic_factor (first second : Adeles) :
    planeUnipotent first second = atInfinity (planeUnipotent first.1 second.1) *
      atFinite (planeUnipotent first.2 second.2) := by
  rw [atInfinity_planeUnipotent, atFinite_planeUnipotent, ← planeUnipotent_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]

theorem normalizedBoundaryResidue_principal_finite_left
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (principal integral : GL3 IntegralAdeles)
    (reduction : GeneralLinearGroup.map integralReduction principal = 1)
    (matrix : AdelicGL) (finite_eq : finiteGroup matrix = GeneralLinearGroup.map integralEmbedding integral) :
    normalizedBoundaryResidue degree continuation
      (atFinite (GeneralLinearGroup.map integralEmbedding principal) * matrix) =
      normalizedBoundaryResidue degree continuation matrix := by
  have level : (finiteGroup matrix)⁻¹ * GeneralLinearGroup.map integralEmbedding principal *
      finiteGroup matrix ∈ finiteLevel := by
    rw [finite_eq]
    exact integral_principal_finite_conjugate principal integral reduction
  rw [atFinite_left_conjugate]
  exact normalizedBoundaryResidue_finite_level flat continuation_spec ⟨_, level⟩ matrix

theorem normalizedBoundaryResidue_plane_three_finite_removal
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (matrix : AdelicGL)
    (finite_eq : finiteGroup matrix = GeneralLinearGroup.map integralEmbedding integral)
    (first second : Adeles) (first_integral : first.2 ∈ Set.range integralEmbedding)
    (second_integral : second.2 ∈ Set.range integralEmbedding) :
    normalizedBoundaryResidue degree continuation (planeUnipotent (3 * first) (3 * second) * matrix) =
      normalizedBoundaryResidue degree continuation
        (atInfinity (planeUnipotent (3 * first.1) (3 * second.1)) * matrix) := by
  obtain ⟨firstValue, first_eq⟩ := first_integral
  obtain ⟨secondValue, second_eq⟩ := second_integral
  have finite_unipotent : planeUnipotent (3 * first.2) (3 * second.2) =
      GeneralLinearGroup.map integralEmbedding (planeUnipotent (3 * firstValue) (3 * secondValue)) := by
    simp only [map_planeUnipotent, map_mul, map_ofNat, first_eq, second_eq]
  rw [planeUnipotent_adelic_factor]
  change normalizedBoundaryResidue degree continuation
    ((atInfinity (planeUnipotent (3 * first.1) (3 * second.1)) *
      atFinite (planeUnipotent (3 * first.2) (3 * second.2))) * matrix) = _
  rw [atInfinity_atFinite_commute, mul_assoc, finite_unipotent]
  apply normalizedBoundaryResidue_principal_finite_left flat continuation_spec _ integral
    (planeUnipotent_three_reduction firstValue secondValue)
  simpa only [map_mul, finiteGroup_atInfinity, one_mul] using finite_eq

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
