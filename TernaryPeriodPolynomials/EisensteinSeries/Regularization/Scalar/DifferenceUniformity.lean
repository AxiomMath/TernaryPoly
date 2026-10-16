module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ProfileDifferences

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalizedScalarDifferenceProfile_uniformly_small
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) {parameters : Set ℂ} (compact : IsCompact parameters)
    {epsilon : ℝ} (positive : 0 < epsilon) :
    ∀ᶠ shift : RealGL3 in nhds 1, ∀ parameter ∈ parameters, ∀ matrix : AdelicGL,
      inMaximalCompact matrix → ‖normalizedScalarDifferenceProfile flat (atInfinity shift) parameter matrix‖ ≤ epsilon := by
  let K := {matrix : AdelicGL | inMaximalCompact matrix}
  let Y := parameters × K
  let : CompactSpace parameters := isCompact_iff_compactSpace.mp compact
  let : CompactSpace K := isCompact_iff_compactSpace.mp maximalCompact_isCompact
  let input (pair : RealGL3 × Y) : ℂ × {matrix : AdelicGL |
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)} :=
    (pair.2.1.val, ⟨pair.2.2.val * atInfinity pair.1, by
      simpa only [Set.mem_ofPred_eq, map_mul, finiteGroup_atInfinity, mul_one] using pair.2.2.property.2⟩)
  let base (pair : RealGL3 × Y) : ℂ × {matrix : AdelicGL |
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)} :=
    (pair.2.1.val, ⟨pair.2.2.val, pair.2.2.property.2⟩)
  have infinity_continuous : Continuous (atInfinity : RealGL3 → AdelicGL) :=
    combineGL_continuous.comp (continuous_id.prodMk continuous_const)
  have input_continuous : Continuous input :=
    (continuous_subtype_val.comp continuous_snd.fst).prodMk
      (((continuous_subtype_val.comp continuous_snd.snd).mul (infinity_continuous.comp continuous_fst)).subtype_mk _)
  have base_continuous : Continuous base :=
    (continuous_subtype_val.comp continuous_snd.fst).prodMk
      ((continuous_subtype_val.comp continuous_snd.snd).subtype_mk _)
  have difference_continuous : Continuous (fun pair : RealGL3 × Y =>
      ‖normalizedScalarDifferenceProfile flat (atInfinity pair.1) pair.2.1.val pair.2.2.val‖) :=
    (((normalizedScalarProfile_integral_joint_continuous flat).comp input_continuous).sub
      ((normalizedScalarProfile_integral_joint_continuous flat).comp base_continuous)).norm
  have uniform : ∀ᶠ shift : RealGL3 in nhds 1, ∀ point : Y,
      ‖normalizedScalarDifferenceProfile flat (atInfinity shift) point.1.val point.2.val‖ ≤ epsilon := by
    have infinity_one : atInfinity (1 : RealGL3) = (1 : AdelicGL) := by
      apply adelicGroup_eq_of_components <;> simp only [realGroup_atInfinity, finiteGroup_atInfinity, map_one]
    have near := isCompact_univ.eventually_forall_of_forall_eventually
      (X := RealGL3) (Y := Y) (x₀ := 1)
      (P := fun shift point => ‖normalizedScalarDifferenceProfile flat (atInfinity shift) point.1.val point.2.val‖ ≤ epsilon)
      (fun point _ => (difference_continuous.continuousAt (x := (1, point))).eventually
        (ge_mem_nhds (by simpa [normalizedScalarDifferenceProfile, infinity_one] using positive)))
    simpa only [Set.mem_univ, forall_true_left] using near
  filter_upwards [uniform] with shift small
  intro parameter member matrix matrix_compact
  exact small (⟨parameter, member⟩, ⟨matrix, matrix_compact⟩)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
