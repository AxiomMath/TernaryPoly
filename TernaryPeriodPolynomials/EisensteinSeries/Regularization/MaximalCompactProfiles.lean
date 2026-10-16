module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ProfileGrowth
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionParameterContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalizedScalarProfile_finite_level
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (matrix : AdelicGL)
    (level : finiteLevel) :
    normalizedScalarProfile flat parameter (matrix * atFinite level.val) =
      normalizedScalarProfile flat parameter matrix := by
  rw [normalizedScalarProfile, normalizedCuspVector_finite_level]
  rfl

theorem normalizedScalarProfile_parabolic_factor
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parabolic : AdelicGL)
    (parabolic_spec : InPlaneParabolic parabolic) :
    ∃ coefficient : ℂ → ℝ, Continuous coefficient ∧ (∀ parameter, 0 ≤ coefficient parameter) ∧
      ∀ parameter matrix, ‖normalizedScalarProfile flat parameter (parabolic * matrix)‖ =
        coefficient parameter * ‖normalizedScalarProfile flat parameter matrix‖ := by
  obtain ⟨first, second, binary, scalar, factorization⟩ :=
    planeParabolic_factorization parabolic parabolic_spec
  let coefficient (parameter : ℂ) := Real.exp
    ((inductionExponent .plane parameter).re * Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) +
      (-2 * inductionExponent .plane parameter).re * Real.log (adeleNorm scalar : ℝ))
  refine ⟨coefficient, ?_, fun parameter => Real.exp_nonneg _, ?_⟩
  · have exponent_continuous : Continuous (fun parameter : ℂ => inductionExponent .plane parameter) :=
      continuous_const.add (continuous_id.div_const 3)
    exact (((Complex.continuous_re.comp exponent_continuous).mul continuous_const).add
      ((Complex.continuous_re.comp (continuous_const.mul exponent_continuous)).mul continuous_const)).rexp
  · intro parameter matrix
    rw [factorization, mul_assoc, normalizedScalarProfile_unipotent,
      planeLevi_rankOne_binary, mul_assoc, normalizedScalarProfile_rankOne_norm,
      normalizedScalarProfile_binary_norm]
    dsimp only [coefficient]
    rw [Real.exp_add]
    ring

theorem normalizedScalarProfile_finite_slice_majorant
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (bound : ℝ)
    (bounded : ∀ parameter matrix, inMaximalCompact matrix →
      ‖normalizedScalarProfile flat parameter matrix‖ ≤ bound)
    (finiteMatrix : FiniteGL) :
    ∃ majorant : ℂ × RealGL3 → ℝ, Continuous majorant ∧
      ∀ parameter realMatrix,
        ‖normalizedScalarProfile flat parameter (combineGL realMatrix finiteMatrix)‖ ≤
          majorant (parameter, realMatrix) := by
  obtain ⟨finiteParabolic, integralMatrix, decomposition, parabolic⟩ := finite_plane_decomposition finiteMatrix
  obtain ⟨coefficient, coefficient_continuous, coefficient_nonnegative, factor⟩ :=
    normalizedScalarProfile_parabolic_factor flat (atFinite finiteParabolic) (planeParabolic_atFinite parabolic)
  let heightFactor (input : ℂ × RealGL3) : ℝ := Real.exp
    ((inductionExponent .plane input.1).re * Real.log |input.2.val.det| -
      (3 / 2 + input.1.re) * Real.log (realPlaneHeight input.2))
  have height_continuous : Continuous heightFactor := by
    have exponent_continuous : Continuous (fun parameter : ℂ => (inductionExponent .plane parameter).re) :=
      Complex.continuous_re.comp (continuous_const.add (continuous_id.div_const 3))
    have log_det_continuous : Continuous (fun matrix : RealGL3 => Real.log |matrix.val.det|) :=
      Units.continuous_val.matrix_det.abs.log
        (fun matrix => abs_ne_zero.mpr (GeneralLinearGroup.det_ne_zero matrix))
    exact (((exponent_continuous.comp continuous_fst).mul
      (log_det_continuous.comp continuous_snd)).sub
        ((continuous_const.add (Complex.continuous_re.comp continuous_fst)).mul
          ((realPlaneHeight_continuous.comp continuous_snd).log
            (fun input => ne_of_gt (realPlaneHeight_pos input.2))))).rexp
  refine ⟨fun input => coefficient input.1 * (heightFactor input * bound),
    (coefficient_continuous.comp continuous_fst).mul (height_continuous.mul continuous_const), ?_⟩
  intro parameter realMatrix
  have matrix_decomposition : combineGL realMatrix finiteMatrix = atFinite finiteParabolic *
      combineGL realMatrix (GeneralLinearGroup.map integralEmbedding integralMatrix) := by
    apply adelicGroup_eq_of_components
    · simp only [map_mul, realGroup_combineGL, realGroup_atFinite, one_mul]
    · simp only [map_mul, finiteGroup_combineGL, finiteGroup_atFinite, decomposition]
  rw [matrix_decomposition, factor]
  apply mul_le_mul_of_nonneg_left _ (coefficient_nonnegative parameter)
  obtain ⟨compactMatrix, orthogonal, reduction⟩ := normalizedScalarProfile_real_compact_reduction flat
    (combineGL realMatrix (GeneralLinearGroup.map integralEmbedding integralMatrix))
  rw [reduction parameter, realGroup_combineGL, finiteGroup_combineGL]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply bounded
  rw [combineGL_eq_real_finite]
  exact orthogonal_integral_compact compactMatrix _ orthogonal ⟨integralMatrix, rfl⟩

theorem normalizedScalarProfile_locally_bounded_of_maximalCompact_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (bound : ℝ)
    (bounded : ∀ parameter matrix, inMaximalCompact matrix →
      ‖normalizedScalarProfile flat parameter matrix‖ ≤ bound) (base : ℂ × AdelicGL) :
    ∃ localBound : ℝ, ∀ᶠ input : ℂ × AdelicGL in nhds base,
      ‖normalizedScalarProfile flat input.1 input.2‖ ≤ localBound := by
  obtain ⟨majorant, majorant_continuous, majorized⟩ :=
    normalizedScalarProfile_finite_slice_majorant flat bound bounded (finiteGroup base.2)
  let model (input : ℂ × AdelicGL) := majorant (input.1, realGroup input.2)
  have model_continuous : Continuous model :=
    majorant_continuous.comp (continuous_fst.prodMk (realGroup_continuous.comp continuous_snd))
  have near_level : ∀ᶠ input : ℂ × AdelicGL in nhds base,
      (finiteGroup base.2)⁻¹ * finiteGroup input.2 ∈ finiteLevel :=
    (finiteLevel_isOpen.preimage
      (continuous_const.mul (finiteGroup_continuous.comp continuous_snd))).eventually_mem (by simp)
  have near_bound : ∀ᶠ input : ℂ × AdelicGL in nhds base, model input < model base + 1 :=
    (isOpen_lt model_continuous continuous_const).eventually_mem
      (show model base < model base + 1 by linarith)
  refine ⟨model base + 1, ?_⟩
  filter_upwards [near_level, near_bound] with input in_level model_bound
  have correction : input.2 = combineGL (realGroup input.2) (finiteGroup base.2) *
      atFinite ((finiteGroup base.2)⁻¹ * finiteGroup input.2) := by
    rw [combineGL_eq_real_finite, mul_assoc, ← atFinite_mul, mul_inv_cancel_left, ← adelicGroup_real_finite]
  calc
    _ = ‖normalizedScalarProfile flat input.1
        (combineGL (realGroup input.2) (finiteGroup base.2))‖ := by
      conv_lhs => rw [correction, normalizedScalarProfile_finite_level flat input.1 _ ⟨_, in_level⟩]
    _ ≤ model input := majorized input.1 (realGroup input.2)
    _ ≤ model base + 1 := model_bound.le

theorem compact_bound_of_locally_bounded_above
    {X : Type*} [TopologicalSpace X] {function : X → ℝ}
    (locally : ∀ base, ∃ bound : ℝ, ∀ᶠ nearby in nhds base, function nearby ≤ bound)
    {domain : Set X} (compact : IsCompact domain) :
    ∃ bound : ℝ, ∀ point ∈ domain, function point ≤ bound := by
  classical
  choose bounds near using locally
  obtain ⟨centers, _, covers⟩ := compact.elim_nhds_subcover
    (fun center => {point | function point ≤ bounds center}) (fun center _ => near center)
  refine ⟨∑ center ∈ centers, max 0 (bounds center), ?_⟩
  intro point member
  obtain ⟨center, in_centers, below⟩ := Set.mem_iUnion₂.mp (covers member)
  exact below.trans ((le_max_right _ _).trans
    (Finset.single_le_sum (fun other _ => le_max_left 0 (bounds other)) in_centers))

theorem normalizedScalarProfile_compact_bound_of_maximalCompact_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (bound : ℝ)
    (bounded : ∀ parameter matrix, inMaximalCompact matrix →
      ‖normalizedScalarProfile flat parameter matrix‖ ≤ bound)
    (parameters : Set ℂ) (matrices : Set AdelicGL)
    (parameters_compact : IsCompact parameters) (matrices_compact : IsCompact matrices) :
    ∃ compactBound : ℝ, ∀ parameter ∈ parameters, ∀ matrix ∈ matrices,
      ‖normalizedScalarProfile flat parameter matrix‖ ≤ compactBound := by
  obtain ⟨compactBound, compact_bounded⟩ := compact_bound_of_locally_bounded_above
    (normalizedScalarProfile_locally_bounded_of_maximalCompact_bound flat bound bounded)
    (parameters_compact.prod matrices_compact)
  exact ⟨compactBound, fun parameter parameter_in matrix matrix_in =>
    compact_bounded (parameter, matrix) ⟨parameter_in, matrix_in⟩⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
