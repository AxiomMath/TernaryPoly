module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.CuspThetaDecay
public import Mathlib.NumberTheory.Modular

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.CircleCharacters TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealSiegelReduction

theorem chart_I : unit (UpperHalfPlane.I : ℂ) UpperHalfPlane.I.im_pos = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [unit, matrix]

theorem positive_decomposition (point : BinaryRealGL) (positive : 0 < (GeneralLinearGroup.det point).val) :
    ∃ scale : ℝˣ, 0 < scale.val ∧ ∃ rotation : Circle,
      point = GeneralLinearGroup.scalar (Fin 2) scale *
        (unit (point • UpperHalfPlane.I : UpperHalfPlane) (point • UpperHalfPlane.I).im_pos * circleRotation rotation) := by
  let value := UpperHalfPlane.denom point UpperHalfPlane.I
  have nonzero : value ≠ 0 := UpperHalfPlane.denom_ne_zero point UpperHalfPlane.I
  have equality := MobiusChart.chart_factor point positive UpperHalfPlane.I
  rw [chart_I, mul_one, complexUnit_factor] at equality
  refine ⟨Units.mk0 ‖value‖ (norm_ne_zero_iff.mpr nonzero), norm_pos_iff.mpr nonzero, phase value nonzero, ?_⟩
  exact equality.trans (by rw [← mul_assoc, ← GeneralLinearGroup.scalar_commute, mul_assoc])

theorem fd_height (argument : UpperHalfPlane) (membership : argument ∈ ModularGroup.fd) :
    (1 / 2 : ℝ) ≤ argument.im ∧ |argument.re| ≤ 1 / 2 := by
  have property : 0 < (argument : ℂ).im ∧ 1 ≤ ‖(argument : ℂ)‖ ∧ |(argument : ℂ).re| ≤ 1 / 2 := by
    change (argument : ℂ) ∈ {z : ℂ | 0 < z.im ∧ 1 ≤ ‖z‖ ∧ |z.re| ≤ 1 / 2}
    rw [← ModularGroup.coe_fd]
    exact ⟨argument, membership, rfl⟩
  refine ⟨?_, property.2.2⟩
  have normSquare : 1 ≤ ‖(argument : ℂ)‖ ^ 2 := one_le_pow₀ property.2.1
  rw [Complex.sq_norm, Complex.normSq_apply] at normSquare
  change 1 ≤ argument.re * argument.re + argument.im * argument.im at normSquare
  have realBound := abs_le.mp property.2.2
  change -(1 / 2 : ℝ) ≤ argument.re ∧ argument.re ≤ 1 / 2 at realBound
  have realSquare : argument.re ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr realBound.2) (by linarith : 0 ≤ 1 / 2 + argument.re)]
  by_contra small
  have imaginarySquare : argument.im ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 2 - argument.im) (by linarith [argument.im_pos] : 0 ≤ 1 / 2 + argument.im)]
  nlinarith

theorem mapGL_smul (rational : SpecialLinearGroup (Fin 2) ℤ) (argument : UpperHalfPlane) :
    SpecialLinearGroup.mapGL ℝ rational • argument = rational • argument := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (by simp [SpecialLinearGroup.det_mapGL]), UpperHalfPlane.coe_specialLinearGroup_apply]
  rfl

theorem modular_reduction (point : BinaryRealGL) (positive : 0 < (GeneralLinearGroup.det point).val) :
    ∃ rational : SpecialLinearGroup (Fin 2) ℤ, ∃ scale : ℝˣ, 0 < scale.val ∧
      ∃ argument : UpperHalfPlane, argument ∈ ModularGroup.fd ∧ ∃ rotation : Circle,
        point = (SpecialLinearGroup.mapGL ℝ rational)⁻¹ *
          (GeneralLinearGroup.scalar (Fin 2) scale * (unit argument argument.im_pos * circleRotation rotation)) := by
  obtain ⟨rational, membership⟩ := ModularGroup.exists_smul_mem_fd (point • UpperHalfPlane.I)
  let transformed := SpecialLinearGroup.mapGL ℝ rational * point
  have transformedPositive : 0 < (GeneralLinearGroup.det transformed).val := by
    simpa only [transformed, map_mul, SpecialLinearGroup.det_mapGL, Units.val_mul, Units.val_one, one_mul] using positive
  obtain ⟨scale, scalePositive, rotation, equality⟩ := positive_decomposition transformed transformedPositive
  refine ⟨rational, scale, scalePositive, transformed • UpperHalfPlane.I, ?_, rotation, ?_⟩
  · simpa only [transformed, mul_smul, mapGL_smul] using membership
  · rw [← equality]
    exact (inv_mul_cancel_left _ _).symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealSiegelReduction
