module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Siegel.Shells

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelMeasurability TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelShells
open scoped Pointwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelShellMeasure

theorem scale_add (first second : ℝ) : scale (first + second) = scale first * scale second := by
  apply Units.ext
  exact Real.exp_add first second

theorem chart_height (height horizontal logarithm : ℝ) :
    BinaryStrongApproximation.diagonal (scale height) 1 *
        unit (argument (Real.exp (-height) * horizontal) logarithm) (argument (Real.exp (-height) * horizontal) logarithm).im_pos =
      unit (argument horizontal (height + logarithm)) (argument horizontal (height + logarithm)).im_pos := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [BinaryStrongApproximation.diagonal, scale, unit, matrix, argument, Matrix.mul_apply,
      Fin.sum_univ_two, Real.exp_add, Real.exp_neg, ← mul_assoc]

def normalizedHorizontal (natural : ℕ) (horizontal : Horizontal) : Horizontal :=
  ⟨Real.exp (-(natural : ℝ)) * horizontal.val, by
    apply abs_le.mp
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr horizontal.property) (Real.exp_pos _).le).trans
      (by simpa only [mul_one] using Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg natural)))⟩

def normalize (natural : ℕ) (parameter : SiegelShells.Parameter) : SiegelShells.Parameter :=
  (parameter.1, parameter.2.1, parameter.2.2.1, normalizedHorizontal natural parameter.2.2.2.1, parameter.2.2.2.2)

def translation (integer : ℤ) (natural : ℕ) : BinaryAdelicGL :=
  atInfinity (GeneralLinearGroup.scalar (Fin 2) (scale integer) * BinaryStrongApproximation.diagonal (scale natural) 1)

theorem real_factor (integer : ℤ) (natural : ℕ) (first second horizontal : ℝ) (right : BinaryRealGL) :
    GeneralLinearGroup.scalar (Fin 2) (scale ((integer : ℝ) + first)) *
        (unit (argument horizontal ((natural : ℝ) + second)) (argument horizontal ((natural : ℝ) + second)).im_pos * right) =
      (GeneralLinearGroup.scalar (Fin 2) (scale integer) * BinaryStrongApproximation.diagonal (scale natural) 1) *
        (GeneralLinearGroup.scalar (Fin 2) (scale first) *
          (unit (argument (Real.exp (-(natural : ℝ)) * horizontal) second)
            (argument (Real.exp (-(natural : ℝ)) * horizontal) second).im_pos * right)) := by
  rw [scale_add, map_mul, ← chart_height]
  calc
    _ = GeneralLinearGroup.scalar (Fin 2) (scale integer) *
        (GeneralLinearGroup.scalar (Fin 2) (scale first) * BinaryStrongApproximation.diagonal (scale natural) 1) *
        (unit (argument (Real.exp (-(natural : ℝ)) * horizontal) second)
          (argument (Real.exp (-(natural : ℝ)) * horizontal) second).im_pos * right) := by group
    _ = _ := by
      rw [GeneralLinearGroup.scalar_commute (scale first)
        (BinaryStrongApproximation.diagonal (scale natural) 1)]
      group

theorem translated_parameter (integer : ℤ) (natural : ℕ) (parameter : SiegelShells.Parameter) :
    SiegelShells.parameterize integer natural parameter =
      translation integer natural * SiegelShells.parameterize 0 0 (normalize natural parameter) := by
  change atFinite (GeneralLinearGroup.map integralEmbedding parameter.1) *
      atInfinity (GeneralLinearGroup.scalar (Fin 2) (scale ((integer : ℝ) + parameter.2.1.val)) *
        (unit (argument parameter.2.2.2.1.val ((natural : ℝ) + parameter.2.2.1.val)) _ * RealSiegelSet.rightFactor parameter.2.2.2.2)) = _
  rw [real_factor, Height.atInfinity_mul, ← mul_assoc, TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute, mul_assoc]
  simp only [translation, SiegelShells.parameterize, normalize, normalizedHorizontal, AdelicSiegelCover.chart,
    Int.cast_zero, Nat.cast_zero, zero_add]

theorem shell_subset_translate (integer : ℤ) (natural : ℕ) :
    shell integer natural ⊆ translation integer natural • shell 0 0 := by
  rintro point ⟨parameter, rfl⟩
  exact ⟨SiegelShells.parameterize 0 0 (normalize natural parameter), ⟨normalize natural parameter, rfl⟩,
    (translated_parameter integer natural parameter).symm⟩

theorem measure_shell_le (integer : ℤ) (natural : ℕ) :
    BinaryHaar.measure (shell integer natural) ≤ BinaryHaar.measure (shell 0 0) := by
  calc
    _ ≤ BinaryHaar.measure (translation integer natural • shell 0 0) := measure_mono (shell_subset_translate integer natural)
    _ = _ := measure_smul BinaryHaar.measure _ _

theorem core_finite : BinaryHaar.measure (shell 0 0) < ⊤ := (shell_compact 0 0).measure_lt_top

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelShellMeasure
