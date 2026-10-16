module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.HalfPlaneBounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AdmissibleRecoveryOperator

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfileTuples TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleRecoveryOperator
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleHalfPlaneBounds

def rowError {degree : ℕ} (data : InducingData degree) (reference : ℂ) (point : IntegralFiniteGL) (number : ℕ) : ℝ :=
  ∑ key : UniversalFiniteProfiles.Key data,
    RecoveryHalfPlaneBounds.error data reference (atFinite (GeneralLinearGroup.map integralEmbedding point)) key number

def averagedError {degree : ℕ} (data : InducingData degree) (reference : ℂ) (point : IntegralFiniteGL) (number : ℕ) : ℝ :=
  ‖(Fintype.card (FiniteSectionProjection.levelImage data) : ℂ)⁻¹‖ *
    ∑ residue : FiniteSectionProjection.levelImage data,
      ‖FiniteProfileResidues.character data (FiniteSectionProjection.representative data residue)‖ *
        rowError data reference (point * FiniteSectionProjection.representative data residue) number

def error {degree : ℕ} (data : InducingData degree) (reference : ℂ) (number : ℕ) : ℝ :=
  ∑ key : UniversalFiniteProfiles.Key data, averagedError data reference (UniversalFiniteProfiles.representative data key) number

theorem rowError_nonnegative {degree : ℕ} (data : InducingData degree) (reference : ℂ) (point : IntegralFiniteGL) (number : ℕ) :
    0 ≤ rowError data reference point number :=
  Finset.sum_nonneg (fun _ _ => RecoveryHalfPlaneBounds.error_nonnegative data reference _ _ number)

theorem averagedError_nonnegative {degree : ℕ} (data : InducingData degree) (reference : ℂ) (point : IntegralFiniteGL) (number : ℕ) :
    0 ≤ averagedError data reference point number :=
  mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (rowError_nonnegative data reference _ number)))

theorem error_nonnegative {degree : ℕ} (data : InducingData degree) (reference : ℂ) (number : ℕ) :
    0 ≤ error data reference number :=
  Finset.sum_nonneg (fun _ _ => averagedError_nonnegative data reference _ number)

theorem rowError_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) :
    Tendsto (rowError data reference point) atTop (nhds 0) := by
  unfold rowError
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
    (fun key _ => RecoveryHalfPlaneBounds.error_tendsto data reference halfPlane _ ⟨point, rfl⟩ key)

theorem averagedError_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) :
    Tendsto (averagedError data reference point) atTop (nhds 0) := by
  unfold averagedError
  have result := (tendsto_finsetSum Finset.univ (fun residue : FiniteSectionProjection.levelImage data =>
    fun _ => (rowError_tendsto data reference halfPlane (point * FiniteSectionProjection.representative data residue)).const_mul
      ‖FiniteProfileResidues.character data (FiniteSectionProjection.representative data residue)‖)).const_mul
        ‖(Fintype.card (FiniteSectionProjection.levelImage data) : ℂ)⁻¹‖
  simpa only [mul_zero, Finset.sum_const_zero] using result

theorem error_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) : Tendsto (error data reference) atTop (nhds 0) := by
  unfold error
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
    (fun key _ => averagedError_tendsto data reference halfPlane (UniversalFiniteProfiles.representative data key))

theorem row_bound {degree : ℕ} (data : InducingData degree) (reference parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) (number : ℕ)
    (ordered : (reference + number).re ≤ parameter.re) (value : Space data) :
    ‖row data parameter ((RecoveryOperatorLimit.shifted_halfPlane reference halfPlane number).trans ordered) point value -
      primitiveRow data reference halfPlane point value‖ ≤ rowError data reference point number * ‖value‖ := by
  rw [TupleRecoveryOperator.row_apply, primitiveRow_apply, ← Finset.sum_sub_distrib, rowError, Finset.sum_mul]
  apply norm_sum_le_of_le
  intro key _
  calc
    _ ≤ ‖RecoveryCoefficients.operator data parameter
        ((RecoveryOperatorLimit.shifted_halfPlane reference halfPlane number).trans ordered)
        (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key -
      RecoveryOperatorLimit.primitiveOperator data reference halfPlane
        (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key‖ * ‖value key‖ :=
      (RecoveryCoefficients.operator data parameter _ _ ⟨point, rfl⟩ key -
        RecoveryOperatorLimit.primitiveOperator data reference halfPlane _ ⟨point, rfl⟩ key).le_opNorm (value key)
    _ ≤ _ := mul_le_mul (RecoveryHalfPlaneBounds.operator_error_le data reference parameter halfPlane _ ⟨point, rfl⟩ key number ordered)
      (norm_le_pi_norm value key) (norm_nonneg _) (RecoveryHalfPlaneBounds.error_nonnegative data reference _ key number)

theorem projectedRow_bound {degree : ℕ} (data : InducingData degree) (reference parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) (number : ℕ)
    (ordered : (reference + number).re ≤ parameter.re) (value : Space data) :
    ‖projectedRow data parameter ((RecoveryOperatorLimit.shifted_halfPlane reference halfPlane number).trans ordered) point value -
      primitiveProjectedRow data reference halfPlane point value‖ ≤ rowError data reference point number * ‖value‖ := by
  simp only [projectedRow, primitiveProjectedRow, ContinuousLinearMap.comp_apply, ← map_sub]
  calc
    _ ≤ ‖CompactAveraging.averagingOperator data.cusp finiteCongruence‖ *
      ‖row data parameter _ point value - primitiveRow data reference halfPlane point value‖ :=
      (CompactAveraging.averagingOperator data.cusp finiteCongruence).le_opNorm _
    _ ≤ ‖row data parameter _ point value - primitiveRow data reference halfPlane point value‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (CompactAveraging.averagingOperator_norm_le data.cusp finiteCongruence)
    _ ≤ _ := row_bound data reference parameter halfPlane point number ordered value

theorem averagedRow_bound {degree : ℕ} (data : InducingData degree) (reference parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : IntegralFiniteGL) (number : ℕ)
    (ordered : (reference + number).re ≤ parameter.re) (value : Space data) :
    ‖averagedRow data parameter ((RecoveryOperatorLimit.shifted_halfPlane reference halfPlane number).trans ordered) point value -
      primitiveAveragedRow data reference halfPlane point value‖ ≤ averagedError data reference point number * ‖value‖ := by
  simp only [averagedRow, primitiveAveragedRow, _root_.smul_apply, _root_.sum_apply]
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  rw [norm_smul, averagedError, mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply norm_sum_le_of_le
  intro residue _
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (projectedRow_bound data reference parameter halfPlane _ number ordered value) (norm_nonneg _)

theorem operator_bound {degree : ℕ} (data : InducingData degree) (reference parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (number : ℕ)
    (ordered : (reference + number).re ≤ parameter.re) :
    ‖operator data parameter ((RecoveryOperatorLimit.shifted_halfPlane reference halfPlane number).trans ordered) -
      primitiveOperator data reference halfPlane‖ ≤ error data reference number := by
  apply ContinuousLinearMap.opNorm_le_bound _ (error_nonnegative data reference number)
  intro value
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (error_nonnegative data reference number) (norm_nonneg value))).mpr
  intro key
  exact (averagedRow_bound data reference parameter halfPlane _ number ordered value).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum
      (fun key _ => averagedError_nonnegative data reference (UniversalFiniteProfiles.representative data key) number)
      (Finset.mem_univ key)) (norm_nonneg value))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleHalfPlaneBounds
