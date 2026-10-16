module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.ProfileRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameHeight

theorem inverse_lastRow (frame : Rectangular ℝ) (column : Fin 3) :
    inverseMatrix frame 2 column = (RealFrameChart.completion frame).det⁻¹ * exterior frame column := by
  simp only [inverseMatrix, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  congr 1
  fin_cases column <;> simp [Matrix.adjugate_fin_three, RealFrameChart.completion, exterior, crossProduct] <;> ring

def lastRow (frame : Rectangular ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun column => inverseMatrix frame 2 column)

theorem lastRow_norm_sq (frame : Rectangular ℝ) :
    ‖lastRow frame‖ ^ 2 = (RealFrameChart.completion frame).det⁻¹ := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [lastRow, WithLp.ofLp_toLp, inverse_lastRow, norm_mul, Real.norm_eq_abs, sq_abs, mul_pow]
  rw [← Finset.mul_sum, ← RealFrameChart.completion_det]
  field_simp

theorem lastRow_log (frame : Rectangular ℝ) :
    Real.log ‖lastRow frame‖ = -(Real.log (RealFrameChart.completion frame).det) / 2 := by
  have equality := congrArg Real.log (lastRow_norm_sq frame)
  rw [Real.log_pow, Real.log_inv] at equality
  norm_num only [Nat.cast_ofNat] at equality
  linarith

theorem point_val (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    (point frame).val = inverseMatrix frame := by
  rw [point_eq frame fullRank, invertibleMatrix_val _ (inverseMatrix_det_ne_zero frame fullRank)]

theorem point_det_log (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    Real.log |(point frame).val.det| = -Real.log (RealFrameChart.completion frame).det := by
  have determinant := RealProfileRegularity.point_det frame fullRank
  change (point frame).val.det = _ at determinant
  rw [determinant, abs_of_pos (inv_pos.mpr (completion_det_pos frame fullRank)), Real.log_inv]

theorem binary_log (frame : Rectangular ℝ) (fullRank : FullRank frame)
    (parabolic : planeParabolic ℝ) (orthogonal : RealGL3)
    (factorization : point frame = parabolic.val * orthogonal)
    (orthogonality : orthogonal.val.transpose * orthogonal.val = 1)
    (corner : (planeCornerUnit parabolic).val =
      ‖(WithLp.toLp 2 (fun column : Fin 3 => (point frame).val 2 column) : EuclideanSpace ℝ (Fin 3))‖) :
    Real.log |(planeBinaryBlock parabolic).val.det| = -Real.log (RealFrameChart.completion frame).det / 2 := by
  have equality := TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.real_heightLog_formula (point frame) parabolic orthogonal factorization orthogonality corner
  rw [corner, abs_of_nonneg (norm_nonneg _), point_det_log frame fullRank, point_val frame fullRank] at equality
  change (Real.log |(planeBinaryBlock parabolic).val.det| - 2 * Real.log ‖lastRow frame‖) / 3 =
    -Real.log (RealFrameChart.completion frame).det / 3 - Real.log ‖lastRow frame‖ at equality
  rw [lastRow_log frame] at equality
  linarith

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameHeight
