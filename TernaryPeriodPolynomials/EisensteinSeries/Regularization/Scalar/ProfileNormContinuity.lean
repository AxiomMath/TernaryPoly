module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.FamilyNormContinuity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionScalarBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ExponentialFamilyContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalizedScalarProfile_integral_slice_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (finiteMatrix : FiniteGL)
    (finite_integral : finiteMatrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    Continuous (fun realMatrix : RealGL3 => normalizedScalarProfile flat parameter (combineGL realMatrix finiteMatrix)) := by
  apply continuous_iff_continuousAt.mpr
  intro realMatrix
  let vectors (entries : Matrix (Fin 3) (Fin 3) ℝ) :
      cuspFiniteFixedSubmodule inducingData.cusp binaryPrincipalLevel :=
    ⟨normalizedCuspVector flat.1 parameter
        (atInfinity (invertibleMatrix entries) * atFinite finiteMatrix),
      fun binary => normalizedCuspVector_binaryPrincipalLevel_fixed flat.1 parameter _
        (by simpa only [map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul]
              using finite_integral) binary⟩
  have continuous := cusp_family_local_scalar_continuousAt inducingData.cohomological
    vectors realMatrix.val (normalizedCuspVector_centeredMixedOrbit_analyticAt flat.1 parameter finiteMatrix realMatrix)
  have composed := continuous.comp (f := fun matrix : RealGL3 => matrix.val) Units.continuous_val.continuousAt
  simpa only [Function.comp_def, vectors, invertibleMatrix_val, normalizedScalarProfile, combineGL_eq_real_finite] using composed

theorem normalizedScalarProfile_integral_continuousAt
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (base : AdelicGL)
    (finite_integral : finiteGroup base ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    ContinuousAt (normalizedScalarProfile flat parameter) base := by
  have slice_continuous := normalizedScalarProfile_integral_slice_continuous flat parameter (finiteGroup base) finite_integral
  have composed := (slice_continuous.comp realGroup_continuous).continuousAt (x := base)
  have near_level : ∀ᶠ nearby : AdelicGL in nhds base,
      (finiteGroup base)⁻¹ * finiteGroup nearby ∈ finiteLevel :=
    (finiteLevel_isOpen.preimage (continuous_const.mul finiteGroup_continuous)).eventually_mem (by simp)
  apply composed.congr_of_eventuallyEq
  filter_upwards [near_level] with nearby in_level
  have correction : nearby = combineGL (realGroup nearby) (finiteGroup base) *
      atFinite ((finiteGroup base)⁻¹ * finiteGroup nearby) := by
    rw [combineGL_eq_real_finite, mul_assoc, ← atFinite_mul, mul_inv_cancel_left,
      ← adelicGroup_real_finite]
  change normalizedScalarProfile flat parameter nearby = _
  conv_lhs => rw [correction, normalizedScalarProfile_finite_level flat parameter _ ⟨_, in_level⟩]
  rfl

theorem normalizedScalarProfile_integral_joint_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    Continuous (fun input : ℂ × {matrix : AdelicGL |
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)} =>
        normalizedScalarProfile flat input.1 input.2.val) := by
  apply exponential_vector_family_joint_continuous
    (fun parameter (matrix : {matrix : AdelicGL |
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)}) =>
        normalizedScalarProfile flat parameter matrix.val)
  · intro parameter
    apply continuous_iff_continuousAt.mpr
    intro matrix
    exact (normalizedScalarProfile_integral_continuousAt flat parameter matrix.val matrix.property).comp
      continuous_subtype_val.continuousAt
  · intro matrix
    exact normalizedScalarProfile_exponential flat matrix.val

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
