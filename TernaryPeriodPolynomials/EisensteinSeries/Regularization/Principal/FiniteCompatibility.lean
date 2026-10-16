module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.SpecialLinear
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.ResidueSymmetries
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.PlaneDecomposition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem integerGL3_map_map {R S : Type*} [CommRing R] [CommRing S]
    (ringMap : R →+* S) (matrix : IntegralGL3) :
    GeneralLinearGroup.map ringMap (GeneralLinearGroup.map (Int.castRingHom R) matrix) =
      GeneralLinearGroup.map (Int.castRingHom S) matrix := by
  apply Units.ext
  ext row column
  exact map_intCast ringMap (matrix.val row column)

theorem specialLinear_toGL_map {R S : Type*} [CommRing R] [CommRing S]
    (ringMap : R →+* S) (matrix : SpecialLinearGroup (Fin 3) R) :
    GeneralLinearGroup.map ringMap (SpecialLinearGroup.toGL matrix) =
      SpecialLinearGroup.toGL (SpecialLinearGroup.map ringMap matrix) := Units.ext rfl

theorem integerGL3_adelic_factor (matrix : IntegralGL3) :
    rationalGroup (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) =
      atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) *
        atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) matrix) := by
  change GeneralLinearGroup.map rationalAdele (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) = _
  rw [integerGL3_map_map]
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, atFinite, combineGL, pairMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      GeneralLinearGroup.map] <;> rfl

theorem principalIntegerSpecialLinear_integral_reduction (matrix : principalIntegerSpecialLinear) :
    GeneralLinearGroup.map integralReduction
      (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) (SpecialLinearGroup.toGL matrix.val)) = 1 := by
  rw [integerGL3_map_map, specialLinear_toGL_map]
  change SpecialLinearGroup.toGL (integerSpecialLinearReduction matrix.val) = 1
  rw [show integerSpecialLinearReduction matrix.val = 1 from matrix.property, map_one]

theorem principalIntegerSpecialLinear_finite_conjugate (matrix : principalIntegerSpecialLinear)
    (integral : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    (GeneralLinearGroup.map integralEmbedding integral)⁻¹ *
        GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) (SpecialLinearGroup.toGL matrix.val) *
      GeneralLinearGroup.map integralEmbedding integral ∈ finiteLevel := by
  refine ⟨integral⁻¹ * GeneralLinearGroup.map (Int.castRingHom IntegralAdeles)
    (SpecialLinearGroup.toGL matrix.val) * integral, ?_, ?_⟩
  · change GeneralLinearGroup.map integralReduction
      (integral⁻¹ * GeneralLinearGroup.map (Int.castRingHom IntegralAdeles)
        (SpecialLinearGroup.toGL matrix.val) * integral) ∈ GeneralEisenstein.rowStabilizer
    simp only [map_mul, map_inv, principalIntegerSpecialLinear_integral_reduction,
      mul_one, inv_mul_cancel, Subgroup.one_mem]
  · simp only [map_mul, map_inv, integerGL3_map_map]

theorem normalizedBoundaryResidue_principal_integer_translation
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (principal : principalIntegerSpecialLinear) (matrix : AdelicGL)
    (integral : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (finite_eq : finiteGroup matrix = GeneralLinearGroup.map integralEmbedding integral) :
    normalizedBoundaryResidue degree continuation
      (atInfinity (SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) principal.val)) * matrix) =
        normalizedBoundaryResidue degree continuation matrix := by
  let realPart := GeneralLinearGroup.map (Int.castRingHom ℝ) (SpecialLinearGroup.toGL principal.val)
  let finitePart := GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) (SpecialLinearGroup.toGL principal.val)
  have level : (finiteGroup matrix)⁻¹ * finitePart * finiteGroup matrix ∈ finiteLevel := by
    rw [finite_eq]
    exact principalIntegerSpecialLinear_finite_conjugate principal integral
  have finite_invariance := normalizedBoundaryResidue_finite_level flat continuation_spec
    ⟨_, level⟩ (atInfinity realPart * matrix)
  have identity : (atInfinity realPart * matrix) *
      atFinite ((finiteGroup matrix)⁻¹ * finitePart * finiteGroup matrix) =
      rationalGroup (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL principal.val)) * matrix := by
    rw [integerGL3_adelic_factor]
    change (atInfinity realPart * matrix) * atFinite ((finiteGroup matrix)⁻¹ * finitePart * finiteGroup matrix) =
      (atInfinity realPart * atFinite finitePart) * matrix
    simp only [mul_assoc]
    rw [atFinite_left_conjugate]
    simp only [mul_assoc]
  rw [identity, normalizedBoundaryResidue_rational_invariant flat continuation_spec] at finite_invariance
  rw [← specialLinear_toGL_map]
  exact finite_invariance.symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
