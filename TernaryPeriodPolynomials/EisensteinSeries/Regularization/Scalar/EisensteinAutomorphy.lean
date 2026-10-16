module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.FiniteCompatibility
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.ResidueMeasurable

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedScalarEisensteinSum (degree : ℕ) (family : ℂ → AdelicGL → ℂ)
    (parameter : ℂ) (matrix : AdelicGL) : ℂ :=
  ∑' flag, eisensteinSummand (unitaryNormalize degree family) parameter matrix flag

theorem normalizedScalarEisensteinSum_rational
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (rational : RationalGL3) (matrix : AdelicGL) :
    normalizedScalarEisensteinSum degree family parameter (rationalGroup rational * matrix) =
      normalizedScalarEisensteinSum degree family parameter matrix := by
  have term (flag : Flags .plane) :
      eisensteinSummand (unitaryNormalize degree family) parameter (rationalGroup rational * matrix) flag =
        eisensteinSummand (unitaryNormalize degree family) parameter matrix (rational⁻¹ • flag) := by
    rw [unitaryNormalize_eisensteinSummand, unitaryNormalize_eisensteinSummand,
      eisensteinSummand_rational_translate (flat.1 _)]
    simp only [map_mul, normPower_mul, rationalGroup, GeneralLinearGroup.map_det, normPower_rational, one_mul]
  unfold normalizedScalarEisensteinSum
  simp_rw [term]
  exact (MulAction.toPerm (β := Flags .plane) rational⁻¹).tsum_eq _

theorem normalizedScalarEisensteinSum_finite_level
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (level : finiteLevel) (matrix : AdelicGL) :
    normalizedScalarEisensteinSum degree family parameter (matrix * atFinite level.val) =
      normalizedScalarEisensteinSum degree family parameter matrix := by
  apply tsum_congr
  intro flag
  change unitaryNormalize degree family parameter (rationalGroup flag.out⁻¹ * (matrix * atFinite level.val)) = _
  rw [← mul_assoc]
  exact unitaryNormalize_finite_level flat.1 parameter level _

theorem adelic_function_principal_integer_translation (function : AdelicGL → ℂ)
    (rational_invariant : ∀ rational : RationalGL3, ∀ matrix, function (rationalGroup rational * matrix) = function matrix)
    (finite_invariant : ∀ level : finiteLevel, ∀ matrix, function (matrix * atFinite level.val) = function matrix)
    (principal : principalIntegerSpecialLinear) (matrix : AdelicGL)
    (integral : GL3 IntegralAdeles)
    (finite_eq : finiteGroup matrix = GeneralLinearGroup.map integralEmbedding integral) :
    function (atInfinity (SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) principal.val)) * matrix) =
      function matrix := by
  let realPart := GeneralLinearGroup.map (Int.castRingHom ℝ) (SpecialLinearGroup.toGL principal.val)
  let finitePart := GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) (SpecialLinearGroup.toGL principal.val)
  have level : (finiteGroup matrix)⁻¹ * finitePart * finiteGroup matrix ∈ finiteLevel := by
    rw [finite_eq]
    exact principalIntegerSpecialLinear_finite_conjugate principal integral
  have finite_identity := finite_invariant ⟨_, level⟩ (atInfinity realPart * matrix)
  have identity : (atInfinity realPart * matrix) *
      atFinite ((finiteGroup matrix)⁻¹ * finitePart * finiteGroup matrix) =
      rationalGroup (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL principal.val)) * matrix := by
    rw [integerGL3_adelic_factor]
    change (atInfinity realPart * matrix) * atFinite ((finiteGroup matrix)⁻¹ * finitePart * finiteGroup matrix) =
      (atInfinity realPart * atFinite finitePart) * matrix
    simp only [mul_assoc]
    rw [atFinite_left_conjugate]
    simp only [mul_assoc]
  rw [identity, rational_invariant] at finite_identity
  rw [← specialLinear_toGL_map]
  exact finite_identity.symm

theorem normalizedScalarEisensteinSum_principal_integer_translation
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (principal : principalIntegerSpecialLinear) (matrix : AdelicGL) (integral : GL3 IntegralAdeles)
    (finite_eq : finiteGroup matrix = GeneralLinearGroup.map integralEmbedding integral) :
    normalizedScalarEisensteinSum degree family parameter
      (atInfinity (SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) principal.val)) * matrix) =
        normalizedScalarEisensteinSum degree family parameter matrix :=
  adelic_function_principal_integer_translation _ (normalizedScalarEisensteinSum_rational flat parameter)
    (normalizedScalarEisensteinSum_finite_level flat parameter) principal matrix integral finite_eq

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
