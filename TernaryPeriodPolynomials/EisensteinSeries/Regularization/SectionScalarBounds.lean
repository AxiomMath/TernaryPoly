module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.LocalScalarBound
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.MixedDerivatives
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.MaximalCompactProfiles

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalizedCuspVector_centeredMixedOrbit_analyticAt
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (finiteMatrix : FiniteGL) (realMatrix : RealGL3) :
    AnalyticAt ℝ
      (fun input : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 3) (Fin 3) ℝ =>
        cuspCenteredMatrixOrbit inducingData.cusp
          (normalizedCuspVector induced parameter
            (atInfinity (invertibleMatrix input.2) * atFinite finiteMatrix)).val input.1)
      (0, realMatrix.val) := by
  have smooth := (normalizedCuspVector_mixedOrbit_contDiffOn induced parameter finiteMatrix).contDiffAt
    (((invertibleMatrixTuples_isOpen 3 1).prod (invertibleMatrixTuples_isOpen 2 1)).mem_nhds
      (show ((fun _ : Fin 1 => realMatrix.val), (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ))) ∈
          ({entries | ∀ index, (entries index).det ≠ 0} ×ˢ
            {entries | ∀ index, (entries index).det ≠ 0}) from
        ⟨fun _ => realMatrix.det_ne_zero, fun _ => by simp⟩))
  have input_smooth : ContDiffAt ℝ ⊤
      (fun input : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 3) (Fin 3) ℝ =>
        ((fun _ : Fin 1 => input.2), (fun _ : Fin 1 => 1 + input.1))) (0, realMatrix.val) :=
    (contDiffAt_pi.mpr (fun _ => contDiffAt_snd)).prodMk
      (contDiffAt_pi.mpr (fun _ => contDiffAt_const.add contDiffAt_fst))
  have smooth_at_image : ContDiffAt ℝ ⊤
      (fun input : (Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        inducingData.cusp.π (atInfinity (invertibleMatrix (input.2 0)))
          (normalizedCuspVector induced parameter
            (atInfinity (invertibleMatrix (input.1 0)) * atFinite finiteMatrix)).val)
      ((fun _ : Fin 1 => realMatrix.val), (fun _ : Fin 1 => 1 + (0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    simpa only [add_zero] using smooth
  exact (smooth_at_image.comp (0, realMatrix.val) input_smooth).analyticAt

theorem normalizedScalarProfile_integral_slice_locally_bounded
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (finiteMatrix : FiniteGL)
    (finite_integral : finiteMatrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (realMatrix : RealGL3) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ nearby in nhds realMatrix,
      ‖normalizedScalarProfile flat parameter (combineGL nearby finiteMatrix)‖ ≤ bound := by
  let vectors (entries : Matrix (Fin 3) (Fin 3) ℝ) :
      cuspFiniteFixedSubmodule inducingData.cusp binaryPrincipalLevel :=
    ⟨normalizedCuspVector flat.1 parameter
        (atInfinity (invertibleMatrix entries) * atFinite finiteMatrix),
      fun binary => normalizedCuspVector_binaryPrincipalLevel_fixed flat.1 parameter _
        (by simpa only [map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul]
              using finite_integral) binary⟩
  obtain ⟨bound, nonnegative, bounded⟩ := cusp_family_local_scalar_bound inducingData.cohomological
    vectors realMatrix.val (normalizedCuspVector_centeredMixedOrbit_analyticAt flat.1 parameter finiteMatrix realMatrix)
  refine ⟨bound, nonnegative, ?_⟩
  have near := Units.continuous_val.continuousAt bounded
  filter_upwards [near] with nearby nearby_bound
  change ‖cuspBoundedRealization inducingData.cusp (vectors nearby.val).val‖ ≤ bound at nearby_bound
  simpa only [vectors, invertibleMatrix_val, normalizedScalarProfile, combineGL_eq_real_finite]
    using nearby_bound

theorem normalizedScalarProfile_integral_locally_bounded
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (base : AdelicGL)
    (finite_integral : finiteGroup base ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ nearby in nhds base,
      ‖normalizedScalarProfile flat parameter nearby‖ ≤ bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedScalarProfile_integral_slice_locally_bounded
    flat parameter (finiteGroup base) finite_integral (realGroup base)
  have near_real := realGroup_continuous.continuousAt bounded
  have near_level : ∀ᶠ nearby : AdelicGL in nhds base,
      (finiteGroup base)⁻¹ * finiteGroup nearby ∈ finiteLevel :=
    (finiteLevel_isOpen.preimage
      (continuous_const.mul finiteGroup_continuous)).eventually_mem (by simp)
  refine ⟨bound, nonnegative, ?_⟩
  filter_upwards [near_real, near_level] with nearby real_bound in_level
  have correction : nearby = combineGL (realGroup nearby) (finiteGroup base) *
      atFinite ((finiteGroup base)⁻¹ * finiteGroup nearby) := by
    rw [combineGL_eq_real_finite, mul_assoc, ← atFinite_mul, mul_inv_cancel_left,
      ← adelicGroup_real_finite]
  calc
    _ = ‖normalizedScalarProfile flat parameter (combineGL (realGroup nearby) (finiteGroup base))‖ := by
      conv_lhs => rw [correction, normalizedScalarProfile_finite_level flat parameter _ ⟨_, in_level⟩]
    _ ≤ bound := real_bound

theorem normalizedScalarProfile_maximalCompact_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter matrix, inMaximalCompact matrix →
      ‖normalizedScalarProfile flat parameter matrix‖ ≤ bound := by
  let X := {matrix : AdelicGL | inMaximalCompact matrix}
  let : CompactSpace X := isCompact_iff_compactSpace.mp maximalCompact_isCompact
  have locally : ∀ base : X, ∃ bound : ℝ, ∀ᶠ nearby in nhds base,
      ‖normalizedScalarProfile flat 0 nearby.val‖ ≤ bound := by
    intro base
    obtain ⟨bound, _, bounded⟩ := normalizedScalarProfile_integral_locally_bounded
      flat 0 base.val base.property.2
    exact ⟨bound, continuous_subtype_val.continuousAt bounded⟩
  obtain ⟨bound, bounded⟩ := compact_bound_of_locally_bounded_above locally isCompact_univ
  refine ⟨max 0 bound, le_max_left _ _, ?_⟩
  intro parameter matrix compact
  rw [normalizedScalarProfile_flat_compact flat parameter matrix compact]
  exact (bounded ⟨matrix, compact⟩ (Set.mem_univ _)).trans (le_max_right _ _)

theorem normalizedScalarProfile_compact_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (parameters : Set ℂ) (matrices : Set AdelicGL)
    (parameters_compact : IsCompact parameters) (matrices_compact : IsCompact matrices) :
    ∃ bound : ℝ, ∀ parameter ∈ parameters, ∀ matrix ∈ matrices,
      ‖normalizedScalarProfile flat parameter matrix‖ ≤ bound := by
  obtain ⟨bound, _, bounded⟩ := normalizedScalarProfile_maximalCompact_bound flat
  exact normalizedScalarProfile_compact_bound_of_maximalCompact_bound flat bound bounded
    parameters matrices parameters_compact matrices_compact

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
