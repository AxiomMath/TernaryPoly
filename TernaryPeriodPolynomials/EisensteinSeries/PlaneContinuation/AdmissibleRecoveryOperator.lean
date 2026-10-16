module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.ParameterShift
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section


open GeneralEisenstein Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfileTuples

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdmissibleRecoveryOperator

abbrev Space {degree : ℕ} (data : InducingData degree) := ProfileTuples.admissible data

instance completeSpace {degree : ℕ} (data : InducingData degree) : CompleteSpace (Space data) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (ProfileTuples.generators data)).topologicalClosure)

instance operatorNormedRing {degree : ℕ} (data : InducingData degree) :
    NormedRing (Space data →L[ℂ] Space data) := ContinuousLinearMap.toNormedRing

instance operatorNormedSpace {degree : ℕ} (data : InducingData degree) :
    NormedSpace ℂ (Space data →L[ℂ] Space data) := ContinuousLinearMap.toNormedSpace

instance tupleOperatorNormedRing {degree : ℕ} (data : InducingData degree) :
    NormedRing (ProfileTuples.Space data →L[ℂ] ProfileTuples.Space data) := ContinuousLinearMap.toNormedRing

def operator {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) : Space data →L[ℂ] Space data :=
  (TupleRecoveryOperator.operator data parameter halfPlane).restrict
    (TupleParameterShift.operator_preserves data parameter halfPlane)

theorem operator_val {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (value : Space data) :
    (operator data parameter halfPlane value).val =
      TupleRecoveryOperator.operator data parameter halfPlane value.val := rfl

theorem difference_norm {degree : ℕ} (data : InducingData degree) (parameter reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (referenceHalfPlane : -(degree : ℝ) / 2 ≤ reference.re) :
    ‖operator data parameter halfPlane - (FinitePrimitiveRecovery.mass : ℂ) • ContinuousLinearMap.id ℂ (Space data)‖ ≤
      ‖TupleRecoveryOperator.operator data parameter halfPlane -
        TupleRecoveryOperator.primitiveOperator data reference referenceHalfPlane‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro value
  change ‖TupleRecoveryOperator.operator data parameter halfPlane value.val -
    (FinitePrimitiveRecovery.mass : ℂ) • value.val‖ ≤ _ * ‖value.val‖
  rw [← PrimitiveTupleIdentity.admissible_identity data reference referenceHalfPlane value.val value.property]
  exact (TupleRecoveryOperator.operator data parameter halfPlane -
    TupleRecoveryOperator.primitiveOperator data reference referenceHalfPlane).le_opNorm value.val

theorem operator_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) :
    Tendsto (fun index : ℕ => operator data (reference + index)
      (RecoveryOperatorLimit.shifted_halfPlane reference halfPlane index)) atTop
        (nhds ((FinitePrimitiveRecovery.mass : ℂ) • ContinuousLinearMap.id ℂ (Space data))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ : ℕ => norm_nonneg _)
    (fun index : ℕ => difference_norm data (reference + index) reference
      (RecoveryOperatorLimit.shifted_halfPlane reference halfPlane index) halfPlane)
  exact tendsto_iff_norm_sub_tendsto_zero.mp (TupleRecoveryOperator.operator_tendsto data reference halfPlane)

theorem unscale_unit {degree : ℕ} (data : InducingData degree) (scalar : ℂ) (nonzero : scalar ≠ 0)
    (linear : Space data →L[ℂ] Space data) (scaled : IsUnit (scalar • linear)) : IsUnit linear := by
  have bijective := ContinuousLinearMap.isUnit_iff_bijective.mp scaled
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  constructor
  · intro first second equality
    exact bijective.1 (congrArg (fun value : Space data => scalar • value) equality)
  · intro value
    obtain ⟨source, equality⟩ := bijective.2 (scalar • value)
    exact ⟨source, (smul_right_inj nonzero).mp equality⟩

theorem isUnit_of_difference_norm_lt {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (bound : ‖operator data parameter halfPlane -
      (FinitePrimitiveRecovery.mass : ℂ) • ContinuousLinearMap.id ℂ (Space data)‖ < FinitePrimitiveRecovery.mass) :
    IsUnit (operator data parameter halfPlane) := by
  let current := operator data parameter halfPlane
  have identity : (FinitePrimitiveRecovery.mass : ℂ)⁻¹ • current - 1 =
      (FinitePrimitiveRecovery.mass : ℂ)⁻¹ • (current - (FinitePrimitiveRecovery.mass : ℂ) • 1) := by
    rw [smul_sub, inv_smul_smul₀ FinitePrimitiveRecovery.mass_nonzero]
  have small : ‖1 - (FinitePrimitiveRecovery.mass : ℂ)⁻¹ • current‖ < 1 := by
    rw [norm_sub_rev, identity, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos FinitePrimitiveRecovery.mass_pos]
    exact (inv_mul_lt_one₀ FinitePrimitiveRecovery.mass_pos).mpr bound
  have normalized : IsUnit ((FinitePrimitiveRecovery.mass : ℂ)⁻¹ • current) := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one small
  exact unscale_unit data _ (inv_ne_zero FinitePrimitiveRecovery.mass_nonzero) current normalized

theorem eventually_isUnit {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) :
    ∀ᶠ index : ℕ in atTop, IsUnit (operator data (reference + index)
      (RecoveryOperatorLimit.shifted_halfPlane reference halfPlane index)) := by
  have limit := (operator_tendsto data reference halfPlane).const_smul (FinitePrimitiveRecovery.mass : ℂ)⁻¹
  rw [inv_smul_smul₀ FinitePrimitiveRecovery.mass_nonzero] at limit
  have small := (tendsto_iff_norm_sub_tendsto_zero.mp limit).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [small] with index bound
  let current := operator data (reference + index) (RecoveryOperatorLimit.shifted_halfPlane reference halfPlane index)
  have normalized : IsUnit ((FinitePrimitiveRecovery.mass : ℂ)⁻¹ • current) := by
    have bound' : ‖1 - (FinitePrimitiveRecovery.mass : ℂ)⁻¹ • current‖ < 1 := by
      rw [norm_sub_rev]
      exact bound
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one bound'
  exact unscale_unit data _ (inv_ne_zero FinitePrimitiveRecovery.mass_nonzero) current normalized

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdmissibleRecoveryOperator
