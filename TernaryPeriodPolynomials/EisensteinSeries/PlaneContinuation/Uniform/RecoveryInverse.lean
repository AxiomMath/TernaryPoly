module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.HalfPlaneBounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.ModeMatrix
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MeromorphicMatrixInverse

@[expose] public section


open GeneralEisenstein Matrix Filter

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformRecoveryInverse

theorem exists_cutoff {degree : ℕ} (data : InducingData degree) :
    ∃ cutoff : ℝ, (1 - (degree : ℝ)) / 2 < cutoff ∧
      ∀ parameter : ℂ, cutoff ≤ parameter.re →
        ∃ halfPlane : -(degree : ℝ) / 2 ≤ parameter.re,
          IsUnit (AdmissibleRecoveryOperator.operator data parameter halfPlane) := by
  have referenceHalfPlane : -(degree : ℝ) / 2 ≤ (1 : ℂ).re := by
    simp only [Complex.one_re]
    have := Nat.cast_nonneg (α := ℝ) degree
    linarith
  obtain ⟨number, small⟩ := ((TupleHalfPlaneBounds.error_tendsto data 1 referenceHalfPlane).eventually
    (gt_mem_nhds FinitePrimitiveRecovery.mass_pos)).exists
  refine ⟨1 + number, ?_, ?_⟩
  · have := Nat.cast_nonneg (α := ℝ) degree
    have := Nat.cast_nonneg (α := ℝ) number
    linarith
  · intro parameter above
    have ordered : ((1 : ℂ) + number).re ≤ parameter.re := by
      simpa only [Complex.add_re, Complex.one_re, Complex.natCast_re] using above
    have halfPlane := (RecoveryOperatorLimit.shifted_halfPlane 1 referenceHalfPlane number).trans ordered
    refine ⟨halfPlane, AdmissibleRecoveryOperator.isUnit_of_difference_norm_lt data parameter halfPlane ?_⟩
    exact ((AdmissibleRecoveryOperator.difference_norm data parameter 1 halfPlane referenceHalfPlane).trans
      (TupleHalfPlaneBounds.operator_bound data 1 parameter referenceHalfPlane number ordered)).trans_lt small

theorem exists_mode_cutoff {degree : ℕ} (data : InducingData degree) :
    ∃ cutoff : ℝ, (1 - (degree : ℝ)) / 2 < cutoff ∧
      ∀ parameter : ℂ, cutoff ≤ parameter.re → ∀ index : ℤ,
        ∀ halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re,
          IsUnit (TupleModeRestriction.restricted data parameter halfPlane index) := by
  obtain ⟨cutoff, bound, invertible⟩ := exists_cutoff data
  refine ⟨cutoff, bound, ?_⟩
  intro parameter above index halfPlane
  obtain ⟨_, unit⟩ := invertible parameter above
  exact TupleModeRestriction.restricted_isUnit data parameter halfPlane index unit

theorem exists_meromorphic_inverse {degree : ℕ} (data : InducingData degree) (index : ℤ)
    {Indices : Type*} [Fintype Indices] [DecidableEq Indices]
    (basis : Module.Basis Indices ℂ (TupleModeRestriction.admissible data index)) :
    ∃ matrix inverse : ℂ → Matrix Indices Indices ℂ, ∃ cutoff : ℝ,
      (1 - (degree : ℝ)) / 2 < cutoff ∧
      (∀ row column parameter, MeromorphicAt (fun parameter => matrix parameter row column) parameter) ∧
      (∀ row column parameter, MeromorphicAt (fun parameter => inverse parameter row column) parameter) ∧
      ∀ parameter : ℂ, cutoff ≤ parameter.re →
        ∀ halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re,
          matrix parameter = LinearMap.toMatrix basis basis (TupleModeRestriction.restricted data parameter halfPlane index) ∧
          inverse parameter * matrix parameter = 1 ∧ matrix parameter * inverse parameter = 1 := by
  obtain ⟨matrix, meromorphic, equality⟩ := TupleModeMatrix.exists_matrix data index basis
  obtain ⟨cutoff, bound, invertible⟩ := exists_mode_cutoff data
  refine ⟨matrix, (fun parameter => (matrix parameter)⁻¹), cutoff, bound, meromorphic, ?_, ?_⟩
  · intro row column parameter
    exact MeromorphicMatrixInverse.inverse matrix parameter (fun row column => meromorphic row column parameter) row column
  · intro parameter above halfPlane
    have unit : IsUnit (matrix parameter) := by
      rw [equality parameter halfPlane]
      exact (LinearMap.isUnit_toMatrix_iff basis).mpr (invertible parameter above index halfPlane)
    have determinant := (Matrix.isUnit_iff_isUnit_det (matrix parameter)).mp unit
    exact ⟨equality parameter halfPlane, (matrix parameter).nonsing_inv_mul determinant,
      (matrix parameter).mul_nonsing_inv determinant⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformRecoveryInverse
