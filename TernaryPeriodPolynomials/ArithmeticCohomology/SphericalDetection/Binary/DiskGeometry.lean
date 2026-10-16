module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarSlash

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Cayley coordinates centered at the usual upper half-plane basepoint. -/
def binaryDiskPoint (point : ℂ) : ℂ := Complex.I * (1 + point) / (1 - point)

def binaryDiskCoordinate (point : ℂ) : ℂ := (point - Complex.I) / (point + Complex.I)

theorem binaryDiskPoint_zero : binaryDiskPoint 0 = Complex.I := by
  simp [binaryDiskPoint]

theorem binaryDiskPoint_denominator_ne_zero {point : ℂ} (inside : ‖point‖ < 1) :
    1 - point ≠ 0 := by
  intro equality
  have point_one : point = 1 := (sub_eq_zero.mp equality).symm
  simp [point_one] at inside

theorem binaryDiskPoint_im (point : ℂ) :
    (binaryDiskPoint point).im = (1 - ‖point‖ ^ 2) / Complex.normSq (1 - point) := by
  simp only [binaryDiskPoint, Complex.div_im, Complex.mul_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.sub_re, Complex.sub_im, zero_mul, one_mul, zero_add,
    zero_sub, Complex.sq_norm]
  simp only [Complex.normSq_apply]
  ring

theorem binaryDiskPoint_im_pos {point : ℂ} (inside : ‖point‖ < 1) :
    0 < (binaryDiskPoint point).im := by
  rw [binaryDiskPoint_im]
  apply div_pos
  · nlinarith [norm_nonneg point]
  · exact Complex.normSq_pos.mpr (binaryDiskPoint_denominator_ne_zero inside)

def binaryDiskUpperPoint (point : ℂ) (inside : ‖point‖ < 1) : UpperHalfPlane :=
  ⟨binaryDiskPoint point, binaryDiskPoint_im_pos inside⟩

theorem binaryDiskCoordinate_point {point : ℂ} (inside : ‖point‖ < 1) :
    binaryDiskCoordinate (binaryDiskPoint point) = point := by
  have denominator := binaryDiskPoint_denominator_ne_zero inside
  have upper_denominator : binaryDiskPoint point + Complex.I ≠ 0 := by
    intro equality
    have imaginary := congrArg Complex.im equality
    have positive := binaryDiskPoint_im_pos inside
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at imaginary
    linarith
  unfold binaryDiskCoordinate binaryDiskPoint at *
  field_simp
  ring

theorem binaryDiskPoint_differentiableOn :
    DifferentiableOn ℂ binaryDiskPoint (Metric.ball 0 1) := by
  intro point inside
  have bound : ‖point‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using inside
  exact (((differentiableAt_const _).mul (differentiableAt_const _ |>.add differentiableAt_id)).div
    ((differentiableAt_const _).sub differentiableAt_id)
    (binaryDiskPoint_denominator_ne_zero bound)).differentiableWithinAt

theorem binaryDisk_rotation_inside (angle : Circle) {point : ℂ} (inside : ‖point‖ < 1) :
    ‖(angle : ℂ) ^ (-2 : ℤ) * point‖ < 1 := by
  simpa only [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, one_mul] using inside

theorem circle_mul_zpow_neg_two (angle : Circle) :
    (angle : ℂ) * (angle : ℂ) ^ (-2 : ℤ) = (starRingEnd ℂ) (angle : ℂ) := by
  calc
    _ = (angle : ℂ) ^ (1 + (-2 : ℤ)) := by
      rw [zpow_add₀ (Circle.coe_ne_zero angle), zpow_one]
    _ = (angle : ℂ)⁻¹ := by norm_num
    _ = _ := (Circle.coe_inv angle).symm.trans (Circle.coe_inv_eq_conj angle)

theorem binaryDiskPoint_rotation_denom (angle : Circle) (point : ℂ)
    (inside : ‖point‖ < 1) :
    (1 - point) * UpperHalfPlane.denom (binaryRotations angle) (binaryDiskPoint point) =
      (angle : ℂ) * (1 - (angle : ℂ) ^ (-2 : ℤ) * point) := by
  have denominator := binaryDiskPoint_denominator_ne_zero inside
  rw [mul_sub, mul_one, ← mul_assoc, circle_mul_zpow_neg_two]
  change (1 - point) * ((angle : ℂ).im * binaryDiskPoint point + (angle : ℂ).re) = _
  rw [binaryDiskPoint]
  field_simp
  have real_imaginary := Complex.re_add_im (angle : ℂ)
  have conjugate : (starRingEnd ℂ) (angle : ℂ) =
      ((angle : ℂ).re : ℂ) - ((angle : ℂ).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [conjugate, ← real_imaginary]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, zero_add, mul_one]
  ring

theorem binaryDiskPoint_rotation_numerator (angle : Circle) (point : ℂ)
    (inside : ‖point‖ < 1) :
    (1 - point) * (((angle : ℂ).re : ℂ) * binaryDiskPoint point - ((angle : ℂ).im : ℂ)) =
      Complex.I * ((angle : ℂ) * (1 + (angle : ℂ) ^ (-2 : ℤ) * point)) := by
  have denominator := binaryDiskPoint_denominator_ne_zero inside
  rw [mul_add, mul_one, ← mul_assoc, circle_mul_zpow_neg_two, binaryDiskPoint]
  field_simp
  have conjugate : (starRingEnd ℂ) (angle : ℂ) =
      ((angle : ℂ).re : ℂ) - ((angle : ℂ).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [conjugate, ← Complex.re_add_im (angle : ℂ)]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, zero_add, mul_one]
  linear_combination (((angle : ℂ).im : ℂ) * (point - 1)) * Complex.I_mul_I

theorem binaryDiskPoint_rotation (angle : Circle) (point : ℂ) (inside : ‖point‖ < 1) :
    ((binaryRotations angle • binaryDiskUpperPoint point inside : UpperHalfPlane) : ℂ) =
      binaryDiskPoint ((angle : ℂ) ^ (-2 : ℤ) * point) := by
  have positive : 0 < (binaryRotations angle).val.det := by
    change 0 < (Matrix.GeneralLinearGroup.det (binaryRotations angle)).val
    rw [binaryRotations_det]
    norm_num
  rw [UpperHalfPlane.coe_smul_of_det_pos positive]
  change ((((angle : ℂ).re : ℂ) * binaryDiskPoint point + ((-(angle : ℂ).im : ℝ) : ℂ)) /
    UpperHalfPlane.denom (binaryRotations angle) (binaryDiskPoint point)) = _
  rw [Complex.ofReal_neg, ← sub_eq_add_neg]
  have denominator := binaryDiskPoint_denominator_ne_zero inside
  have rotated_denominator := binaryDiskPoint_denominator_ne_zero (binaryDisk_rotation_inside angle inside)
  have numerator_formula :
      (((angle : ℂ).re : ℂ) * binaryDiskPoint point - ((angle : ℂ).im : ℂ)) =
        Complex.I * ((angle : ℂ) * (1 + (angle : ℂ) ^ (-2 : ℤ) * point)) / (1 - point) := by
    apply (eq_div_iff denominator).mpr
    simpa only [mul_comm (1 - point)] using binaryDiskPoint_rotation_numerator angle point inside
  have denominator_formula :
      UpperHalfPlane.denom (binaryRotations angle) (binaryDiskPoint point) =
        (angle : ℂ) * (1 - (angle : ℂ) ^ (-2 : ℤ) * point) / (1 - point) := by
    apply (eq_div_iff denominator).mpr
    simpa only [mul_comm (1 - point)] using binaryDiskPoint_rotation_denom angle point inside
  rw [numerator_formula, denominator_formula, binaryDiskPoint]
  field_simp


end TernaryPeriodPolynomials.SphericalDetection.Helpers
