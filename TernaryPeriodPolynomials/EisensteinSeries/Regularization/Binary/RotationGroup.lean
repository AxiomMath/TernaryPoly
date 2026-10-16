module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.RotationGap
public import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

def binaryComplexMatrix (value : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![value.re, value.im; -value.im, value.re]

theorem binaryComplexMatrix_one : binaryComplexMatrix 1 = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [binaryComplexMatrix]

theorem binaryComplexMatrix_mul (first second : ℂ) :
    binaryComplexMatrix (first * second) = binaryComplexMatrix first * binaryComplexMatrix second := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryComplexMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem binaryComplexMatrix_det (value : ℂ) : (binaryComplexMatrix value).det = Complex.normSq value := by
  simp [binaryComplexMatrix, Matrix.det_fin_two, Complex.normSq_apply]

noncomputable def binaryCircleRotation : Circle →* BinaryRealGL where
  toFun value := GeneralLinearGroup.mkOfDetNeZero (binaryComplexMatrix value)
    (by rw [binaryComplexMatrix_det, Circle.normSq_coe]; exact one_ne_zero)
  map_one' := by
    apply Units.ext
    exact binaryComplexMatrix_one
  map_mul' first second := by
    apply Units.ext
    exact binaryComplexMatrix_mul first second

theorem binaryCircleRotation_val (value : Circle) :
    (binaryCircleRotation value).val = binaryComplexMatrix value := rfl

theorem binaryCircleRotation_val_continuous : Continuous (fun value : Circle => (binaryCircleRotation value).val) := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  fin_cases row <;> fin_cases column <;>
    change Continuous (fun value : Circle => _)
  · change Continuous (fun value : Circle => (value : ℂ).re)
    fun_prop
  · change Continuous (fun value : Circle => (value : ℂ).im)
    fun_prop
  · change Continuous (fun value : Circle => -(value : ℂ).im)
    fun_prop
  · change Continuous (fun value : Circle => (value : ℂ).re)
    fun_prop

theorem binaryCircleRotation_continuous : Continuous binaryCircleRotation := by
  apply Units.continuous_iff.mpr
  refine ⟨binaryCircleRotation_val_continuous, ?_⟩
  simpa only [Function.comp_def, map_inv] using binaryCircleRotation_val_continuous.comp continuous_inv

noncomputable def binaryRotationPath (angle : ℝ) : BinaryRealGL := binaryCircleRotation (Circle.exp angle)

theorem binaryRotationPath_zero : binaryRotationPath 0 = 1 := by simp [binaryRotationPath]

theorem binaryRotationPath_add (first second : ℝ) :
    binaryRotationPath (first + second) = binaryRotationPath first * binaryRotationPath second := by
  simp only [binaryRotationPath, Circle.exp_add, map_mul]

theorem binaryRotationPath_val (angle : ℝ) :
    (binaryRotationPath angle).val = !![Real.cos angle, Real.sin angle; -Real.sin angle, Real.cos angle] := by
  simp [binaryRotationPath, binaryCircleRotation_val, binaryComplexMatrix, Circle.coe_exp,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem binaryRotationPath_entry_hasDerivAt_zero (row column : Fin 2) :
    HasDerivAt (fun angle => (binaryRotationPath angle).val row column) (binaryRotationDirection row column) 0 := by
  simp only [binaryRotationPath_val]
  fin_cases row <;> fin_cases column
  · simpa [binaryRotationDirection] using Real.hasDerivAt_cos 0
  · simpa [binaryRotationDirection] using Real.hasDerivAt_sin 0
  · convert! (Real.hasDerivAt_sin 0).neg using 1
    simp [binaryRotationDirection]
  · simpa [binaryRotationDirection] using Real.hasDerivAt_cos 0

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
