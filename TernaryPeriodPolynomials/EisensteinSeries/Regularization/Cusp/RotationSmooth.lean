module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationAnalyticAverage

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem invertibleMatrix_left_mul (matrix : BinaryRealGL) {vector : Matrix (Fin 2) (Fin 2) ℝ}
    (invertible : vector.det ≠ 0) :
    invertibleMatrix (matrix.val * vector) = matrix * invertibleMatrix vector := by
  have value : matrix.val * vector = (matrix * invertibleMatrix vector).val := by
    simp only [Units.val_mul, invertibleMatrix, dite_eq_left invertible, GeneralLinearGroup.val_mkOfDetNeZero]
  rw [value, invertibleMatrix_val]

theorem cuspCenteredMatrixOrbit_left_translate (cusp : CuspidalRepresentation) (vector : cusp.H)
    (matrix : BinaryRealGL) {point : Matrix (Fin 2) (Fin 2) ℝ} (invertible : point.det ≠ 0) :
    cusp.π (atInfinity matrix) (cuspCenteredMatrixOrbit cusp vector (matrix.inv * point - 1)) =
      cusp.π (atInfinity (invertibleMatrix point)) vector := by
  have shift : 1 + (matrix.inv * point - 1) = matrix.inv * point := by abel
  simp only [cuspCenteredMatrixOrbit, shift]
  rw [show matrix.inv = (matrix⁻¹).val from rfl, invertibleMatrix_left_mul matrix⁻¹ invertible,
    ← Module.End.mul_apply, ← map_mul, ← binary_atInfinity_mul]
  simp only [← mul_assoc, mul_inv_cancel, one_mul]

theorem cuspMatrixOrbit_analyticAt_of_centered (cusp : CuspidalRepresentation) (vector : cusp.H)
    (analytic : AnalyticAt ℝ (cuspCenteredMatrixOrbit cusp vector) 0) (matrix : BinaryRealGL) :
    AnalyticAt ℝ (fun point : Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity (invertibleMatrix point)) vector) matrix.val := by
  let shift : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun point => matrix.inv * point - 1
  have shift_analytic : AnalyticAt ℝ shift matrix.val :=
    (binaryMatrixMultiplication matrix.inv).analyticAt matrix.val |>.sub analyticAt_const
  have at_shift : AnalyticAt ℝ (cuspCenteredMatrixOrbit cusp vector) (shift matrix.val) := by
    simpa only [shift, matrix.inv_val, sub_self] using analytic
  let action := (cuspRealUnitaryAction cusp (atInfinity matrix)).toContinuousLinearMap
  have composed := (action.analyticAt _).comp (at_shift.comp shift_analytic)
  apply composed.congr
  have near : ∀ᶠ point : Matrix (Fin 2) (Fin 2) ℝ in nhds matrix.val, point.det ≠ 0 :=
    (isOpen_ne.preimage continuous_id.matrix_det).mem_nhds matrix.det_ne_zero
  filter_upwards [near] with point invertible
  exact cuspCenteredMatrixOrbit_left_translate cusp vector matrix invertible

theorem cuspRealOrbit_smooth_of_centered (cusp : CuspidalRepresentation) (vector : cusp.H)
    (analytic : AnalyticAt ℝ (cuspCenteredMatrixOrbit cusp vector) 0) :
    Smooth (fun matrices : Fin 1 → BinaryRealGL => cusp.π (atInfinity (matrices 0)) vector) := by
  intro entries member
  have orbit := cuspMatrixOrbit_analyticAt_of_centered cusp vector analytic (invertibleMatrix (entries 0))
  have at_entry : AnalyticAt ℝ (fun point : Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity (invertibleMatrix point)) vector) (entries 0) := by
    simpa only [invertibleMatrix, dite_eq_left (member 0), GeneralLinearGroup.val_mkOfDetNeZero] using orbit
  have composed := at_entry.comp (f := fun tuples : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ => tuples 0)
    (x := entries)
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix (Fin 2) (Fin 2) ℝ) 0).analyticAt entries)
  exact composed.contDiffAt.contDiffWithinAt

theorem cuspRotationProjection_mem_smooth (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) : cuspRotationProjection cusp weight vector.val ∈ cusp.smooth := by
  apply (cusp.smooth_exact _).mpr
  refine ⟨cuspRealOrbit_smooth_of_centered cusp _ (cuspRotationProjection_centeredOrbit_analyticAt cusp weight vector), ?_⟩
  obtain ⟨level, level_open, level_compact, fixed⟩ := ((cusp.smooth_exact vector.val).mp vector.property).2
  exact ⟨level, level_open, level_compact, fun binary =>
    cuspRotationProjection_finite_fixed cusp weight vector.val binary.val (fixed binary)⟩

noncomputable def cuspSmoothRotationProjection (cusp : CuspidalRepresentation) (weight : ℤ) :
    Module.End ℂ cusp.smooth :=
  ((cuspRotationProjection cusp weight).toLinearMap.comp cusp.smooth.subtype).codRestrict cusp.smooth
    (cuspRotationProjection_mem_smooth cusp weight)

theorem cuspSmoothRotationProjection_apply_val (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) :
    (cuspSmoothRotationProjection cusp weight vector).val = cuspRotationProjection cusp weight vector.val := rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
