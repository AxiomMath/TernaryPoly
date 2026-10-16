module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.SiegelReduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealSiegelSet

def half : BinaryRealGL := BinaryStrongApproximation.diagonal (Units.mk0 (1 / 2 : ℝ) (by norm_num)) 1

def doubled (argument : UpperHalfPlane) : UpperHalfPlane :=
  ⟨⟨argument.re, 2 * argument.im⟩, by change 0 < 2 * argument.im; positivity⟩

theorem chart_doubled (argument : UpperHalfPlane) :
    unit argument argument.im_pos = unit (doubled argument) (doubled argument).im_pos * half := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [unit, matrix, half, doubled, BinaryStrongApproximation.diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  ring

def rightFactor (rotation : Circle) : BinaryRealGL := half * circleRotation rotation

def rightSet : Set BinaryRealGL := Set.range rightFactor

theorem rightFactor_continuous : Continuous rightFactor := continuous_const.mul circleRotation_continuous

theorem rightSet_compact : IsCompact rightSet := isCompact_range rightFactor_continuous

theorem decomposition (point : BinaryRealGL) (positive : 0 < (GeneralLinearGroup.det point).val) :
    ∃ rational : SpecialLinearGroup (Fin 2) ℤ, ∃ scale : ℝˣ, 0 < scale.val ∧
      ∃ argument : UpperHalfPlane, 1 ≤ argument.im ∧ |argument.re| ≤ 1 ∧ ∃ right ∈ rightSet,
        point = (SpecialLinearGroup.mapGL ℝ rational)⁻¹ *
          (GeneralLinearGroup.scalar (Fin 2) scale * (unit argument argument.im_pos * right)) := by
  obtain ⟨rational, scale, scalePositive, argument, membership, rotation, equality⟩ :=
    RealSiegelReduction.modular_reduction point positive
  obtain ⟨height, horizontal⟩ := RealSiegelReduction.fd_height argument membership
  refine ⟨rational, scale, scalePositive, doubled argument, ?_, ?_, rightFactor rotation, ⟨rotation, rfl⟩, ?_⟩
  · change 1 ≤ 2 * argument.im
    linarith
  · change |argument.re| ≤ 1
    linarith
  · rw [equality, chart_doubled, mul_assoc]
    rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealSiegelSet
