module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section


open GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem invertibleMatrix_val {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℝ) (invertible : matrix.det ≠ 0) :
    (invertibleMatrix matrix).val = matrix := by
  unfold invertibleMatrix
  rw [dite_eq_left invertible]
  exact GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem invertibleMatrix_coe {dimension : ℕ}
    (matrix : GeneralLinearGroup (Fin dimension) ℝ) :
    invertibleMatrix matrix.val = matrix := by
  unfold invertibleMatrix
  rw [dite_eq_left matrix.det_ne_zero]
  apply Units.ext
  exact GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem invertibleMatrix_inv {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℝ) (invertible : matrix.det ≠ 0) :
    invertibleMatrix matrix⁻¹ = (invertibleMatrix matrix)⁻¹ := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inv, invertibleMatrix_val matrix invertible,
    invertibleMatrix_val matrix⁻¹ (by
      simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using inv_ne_zero invertible)]

theorem invertibleMatrix_mul {dimension : ℕ}
    (first second : Matrix (Fin dimension) (Fin dimension) ℝ)
    (first_invertible : first.det ≠ 0) (second_invertible : second.det ≠ 0) :
    invertibleMatrix (first * second) = invertibleMatrix first * invertibleMatrix second := by
  apply Units.ext
  rw [Units.val_mul, invertibleMatrix_val first first_invertible,
    invertibleMatrix_val second second_invertible,
    invertibleMatrix_val (first * second) (by
      rw [Matrix.det_mul]
      exact mul_ne_zero first_invertible second_invertible)]

theorem smooth_one_contDiffOn {dimension : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {function : GeneralLinearGroup (Fin dimension) ℝ → E}
    (smooth : Smooth (fun point : Fin 1 → GeneralLinearGroup (Fin dimension) ℝ => function (point 0))) :
    ContDiffOn ℝ ⊤ (fun matrix : Matrix (Fin dimension) (Fin dimension) ℝ =>
      function (invertibleMatrix matrix)) {matrix | matrix.det ≠ 0} := by
  have lift_regular : ContDiff ℝ ⊤ (fun matrix : Matrix (Fin dimension) (Fin dimension) ℝ =>
      fun _ : Fin 1 => matrix) := contDiff_pi.mpr (fun _ => contDiff_id)
  exact smooth.comp lift_regular.contDiffOn (fun _ member _ => member)

theorem realGL_contDiffOn_mul_const {dimension : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {order : WithTop ℕ∞}
    (function : GeneralLinearGroup (Fin dimension) ℝ → E)
    (regular : ContDiffOn ℝ order (fun matrix : Matrix (Fin dimension) (Fin dimension) ℝ =>
      function (invertibleMatrix matrix)) {matrix | matrix.det ≠ 0})
    (fixed : GeneralLinearGroup (Fin dimension) ℝ) :
    ContDiffOn ℝ order (fun matrix : Matrix (Fin dimension) (Fin dimension) ℝ =>
      function (invertibleMatrix matrix * fixed)) {matrix | matrix.det ≠ 0} := by
  have multiplication : ContDiff ℝ order
      (fun matrix : Matrix (Fin dimension) (Fin dimension) ℝ => matrix * fixed.val) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    simp only [Matrix.mul_apply]
    exact ContDiff.sum (fun position _ => by fun_prop)
  have composed := regular.comp multiplication.contDiffOn (s := {matrix | matrix.det ≠ 0}) (by
    intro matrix member
    change (matrix * fixed.val).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero member fixed.det_ne_zero)
  apply composed.congr
  intro matrix member
  change function (invertibleMatrix matrix * fixed) = function (invertibleMatrix (matrix * fixed.val))
  rw [invertibleMatrix_mul matrix fixed.val member fixed.det_ne_zero, invertibleMatrix_coe]

theorem realGL_continuous_of_contDiffOn {dimension : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {function : GeneralLinearGroup (Fin dimension) ℝ → E}
    (regular : ContDiffOn ℝ ⊤ (fun matrix : Matrix (Fin dimension) (Fin dimension) ℝ =>
      function (invertibleMatrix matrix)) {matrix | matrix.det ≠ 0}) :
    Continuous function := by
  have matrix_continuous : Continuous
      (fun matrix : GeneralLinearGroup (Fin dimension) ℝ => matrix.val) := Units.continuous_val
  have composed := regular.continuousOn.comp_continuous matrix_continuous
    (fun matrix => GeneralLinearGroup.det_ne_zero matrix)
  simpa only [Function.comp_def, invertibleMatrix_coe] using composed

theorem smooth_continuous {dimension arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {function : (Fin arity → GeneralLinearGroup (Fin dimension) ℝ) → E}
    (smooth : Smooth function) : Continuous function := by
  have matrix_continuous : Continuous
      (fun point : Fin arity → GeneralLinearGroup (Fin dimension) ℝ =>
        fun position => (point position).val) :=
    continuous_pi (fun position => Units.continuous_val.comp (continuous_apply position))
  have composed := smooth.continuousOn.comp_continuous matrix_continuous
    (fun point position => (point position).det_ne_zero)
  simpa only [Function.comp_def, invertibleMatrix_coe] using composed

theorem smooth_analyticAt {dimension arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {function : (Fin arity → GeneralLinearGroup (Fin dimension) ℝ) → E}
    (smooth : Smooth function)
    (point : Fin arity → Matrix (Fin dimension) (Fin dimension) ℝ)
    (invertible : ∀ position, (point position).det ≠ 0) :
    AnalyticAt ℝ (fun matrices : Fin arity → Matrix (Fin dimension) (Fin dimension) ℝ =>
      function (fun position => invertibleMatrix (matrices position))) point := by
  have domain_open : IsOpen {matrices : Fin arity → Matrix (Fin dimension) (Fin dimension) ℝ |
      ∀ position, (matrices position).det ≠ 0} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro position
    exact isOpen_ne_fun (continuous_apply position).matrix_det continuous_const
  exact ((domain_open.contDiffOn_iff).mp smooth invertible).analyticAt

theorem smooth_pair_with_one {dimension : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {function : (Fin 2 → GeneralLinearGroup (Fin dimension) ℝ) → E}
    (smooth : Smooth function) :
    Smooth (fun point : Fin 1 → GeneralLinearGroup (Fin dimension) ℝ => function ![point 0, 1]) := by
  have section_smooth : ContDiff ℝ ⊤
      (fun point : Fin 1 → Matrix (Fin dimension) (Fin dimension) ℝ => ![point 0, 1]) := by
    apply contDiff_pi.mpr
    intro position
    fin_cases position
    · exact contDiff_apply ℝ _ 0
    · exact contDiff_const
  have composed := smooth.comp section_smooth.contDiffOn (s :=
    {point : Fin 1 → Matrix (Fin dimension) (Fin dimension) ℝ |
      ∀ position, (point position).det ≠ 0}) (by
        intro point member position
        fin_cases position
        · exact member 0
        · simp)
  apply composed.congr
  intro point _
  change function ![invertibleMatrix (point 0), 1] =
    function (fun position => invertibleMatrix (![point 0, 1] position))
  congr 1
  funext position
  fin_cases position
  · rfl
  · exact (invertibleMatrix_coe (1 : GeneralLinearGroup (Fin dimension) ℝ)).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
