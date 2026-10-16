module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CocycleDifferential
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.Generators

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CocycleDifferential TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryGenerators
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroCocycleDifferential

theorem fderiv_eq_zero (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (zeroDifferential : hilbertDifferential data degree cocycle = 0) (matrix : BinaryRealGL) :
    fderiv ℝ (matrixCocycle data degree cocycle) matrix.val = 0 := by
  apply ContinuousLinearMap.ext
  intro direction
  have equality := fderiv_cocycle_translate data degree cocycle regularity equation matrix (matrix⁻¹.val * direction)
  rw [zeroDifferential, zero_apply, map_zero] at equality
  have cancellation : matrix.val * (matrix⁻¹.val * direction) = direction := by
    have inverseProduct : matrix.val * matrix⁻¹.val = 1 := matrix.val_inv
    rw [← mul_assoc, inverseProduct, one_mul]
  rw [cancellation] at equality
  exact equality

theorem constant_on_curve (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (zeroDifferential : hilbertDifferential data degree cocycle = 0)
    (curve : ℝ → BinaryRealGL) (curveDifferentiable : Differentiable ℝ (fun time => (curve time).val))
    (first second : ℝ) : cocycle (curve first) = cocycle (curve second) := by
  have derivativeZero (time : ℝ) : HasDerivAt
      (fun time => matrixCocycle data degree cocycle (curve time).val) 0 time := by
    have outer := ((matrixCocycle_contDiffAt data degree cocycle regularity (curve time)).differentiableAt (by simp)).hasFDerivAt
    have composed := outer.comp_hasDerivAt time (curveDifferentiable time).hasDerivAt
    have derivativeValue : fderiv ℝ (matrixCocycle data degree cocycle) (curve time).val = 0 :=
      fderiv_eq_zero data degree cocycle regularity equation zeroDifferential (curve time)
    have zeroValue := congrArg (fun linear : BinaryMatrix →L[ℝ] HilbertVectors data degree =>
      linear (deriv (fun time => (curve time).val) time)) derivativeValue
    exact composed.congr_deriv zeroValue
  have constant := is_const_of_deriv_eq_zero (fun time => (derivativeZero time).differentiableAt)
    (fun time => (derivativeZero time).deriv)
  funext index
  apply Subtype.ext
  have equality := congrFun (constant first second) index
  simpa only [matrixCocycle, invertibleMatrix_units] using equality

noncomputable def kernel (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second)) : Subgroup BinaryRealGL where
  carrier := {matrix | cocycle matrix = 0}
  one_mem' := cocycle_one data degree cocycle equation
  mul_mem' {first second} firstMember secondMember := by
    change cocycle (first * second) = 0
    rw [equation, firstMember, secondMember, map_zero, add_zero]
  inv_mem' {matrix} membership := by
    change cocycle matrix⁻¹ = 0
    have equality := equation matrix matrix⁻¹
    rw [mul_inv_cancel, cocycle_one data degree cocycle equation, membership, zero_add] at equality
    have transformed := congrArg (coefficientAction data degree matrix⁻¹) equality
    rw [map_zero, ← Module.End.mul_apply, ← coefficientAction_mul, inv_mul_cancel,
      coefficientAction_one, Module.End.one_apply] at transformed
    exact transformed.symm

theorem upper_curve_differentiable : Differentiable ℝ (fun time : ℝ => (binaryUnipotent time).val) := by
  apply differentiable_pi.mpr
  intro row
  apply differentiable_pi.mpr
  intro column
  fin_cases row <;> fin_cases column
  · exact differentiable_const _
  · exact differentiable_id
  · exact differentiable_const _
  · exact differentiable_const _

theorem lower_curve_differentiable : Differentiable ℝ (fun time : ℝ => (lowerUnipotent time).val) := by
  apply differentiable_pi.mpr
  intro row
  apply differentiable_pi.mpr
  intro column
  fin_cases row <;> fin_cases column
  · exact differentiable_const _
  · exact differentiable_const _
  · exact differentiable_id
  · exact differentiable_const _

noncomputable def exponentialDiagonal (time : ℝ) : BinaryRealGL :=
  determinantDiagonal (Units.mk0 (Real.exp time) (Real.exp_ne_zero time))

theorem exponentialDiagonal_differentiable : Differentiable ℝ (fun time : ℝ => (exponentialDiagonal time).val) := by
  apply differentiable_pi.mpr
  intro row
  apply differentiable_pi.mpr
  intro column
  fin_cases row <;> fin_cases column
  · exact differentiable_const _
  · exact differentiable_const _
  · exact differentiable_const _
  · exact Real.differentiable_exp

theorem exponentialDiagonal_zero : exponentialDiagonal 0 = 1 := by
  have equality : Units.mk0 (Real.exp 0) (Real.exp_ne_zero 0) = (1 : ℝˣ) := by
    apply Units.ext
    exact Real.exp_zero
  rw [exponentialDiagonal, equality, determinantDiagonal_one]

theorem exponentialDiagonal_log (scalar : ℝˣ) (positive : 0 < scalar.val) :
    exponentialDiagonal (Real.log scalar.val) = determinantDiagonal scalar := by
  have equality : Units.mk0 (Real.exp (Real.log scalar.val)) (Real.exp_ne_zero _) = scalar := by
    apply Units.ext
    exact Real.exp_log positive
  rw [exponentialDiagonal, equality]

theorem positive_cocycle_eq_zero (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (zeroDifferential : hilbertDifferential data degree cocycle = 0)
    (matrix : BinaryRealGL) (positive : 0 < matrix.val.det) : cocycle matrix = 0 := by
  apply positive_det_mem (kernel data degree cocycle equation) ?_ ?_ ?_ matrix positive
  · intro parameter
    change cocycle (binaryUnipotent parameter) = 0
    have equality := constant_on_curve data degree cocycle regularity equation zeroDifferential
      (fun time => binaryUnipotent time) upper_curve_differentiable parameter 0
    simpa only [upper_zero, cocycle_one data degree cocycle equation] using equality
  · intro parameter
    change cocycle (lowerUnipotent parameter) = 0
    have equality := constant_on_curve data degree cocycle regularity equation zeroDifferential
      lowerUnipotent lower_curve_differentiable parameter 0
    simpa only [lower_zero, cocycle_one data degree cocycle equation] using equality
  · intro scalar scalarPositive
    change cocycle (determinantDiagonal scalar) = 0
    have equality := constant_on_curve data degree cocycle regularity equation zeroDifferential
      exponentialDiagonal exponentialDiagonal_differentiable (Real.log scalar.val) 0
    simpa only [exponentialDiagonal_log scalar scalarPositive, exponentialDiagonal_zero,
      cocycle_one data degree cocycle equation] using equality

theorem reflection_det : TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection.val.det = -1 := by
  norm_num [TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection, Matrix.det_fin_two]

theorem positive_fixes_reflection_value (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (positiveZero : ∀ matrix : BinaryRealGL, 0 < matrix.val.det → cocycle matrix = 0)
    (matrix : BinaryRealGL) (positive : 0 < matrix.val.det) :
    coefficientAction data degree matrix (cocycle TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection) =
      cocycle TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection := by
  let reflection := TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection
  have conjugatePositive : 0 < (reflection * matrix * reflection).val.det := by
    change 0 < (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection * matrix * TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection).val.det
    simpa only [Units.val_mul, Matrix.det_mul, reflection_det, neg_one_mul, mul_neg_one, neg_neg] using positive
  have productEquality : reflection * (reflection * matrix * reflection) = matrix * reflection := by
    calc
      _ = (reflection * reflection) * matrix * reflection := by group
      _ = matrix * reflection := by rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection_mul_self, one_mul]
  have first := equation reflection (reflection * matrix * reflection)
  rw [productEquality, positiveZero _ conjugatePositive, map_zero, add_zero] at first
  have second := equation matrix reflection
  rw [positiveZero matrix positive, zero_add] at second
  exact second.symm.trans first

theorem coboundary_of_positive_vanishing (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (positiveZero : ∀ matrix : BinaryRealGL, 0 < matrix.val.det → cocycle matrix = 0) :
    ∃ vectors : Vectors data degree, ∀ matrix,
      cocycle matrix = coefficientAction data degree matrix vectors - vectors := by
  let reflection := TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection
  have reflectionAction : coefficientAction data degree reflection (cocycle reflection) = -cocycle reflection := by
    have equality := equation reflection reflection
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection_mul_self, cocycle_one data degree cocycle equation] at equality
    exact eq_neg_of_add_eq_zero_right equality.symm
  refine ⟨(-(1 / 2 : ℂ)) • cocycle reflection, ?_⟩
  intro matrix
  by_cases positive : 0 < matrix.val.det
  · rw [positiveZero matrix positive, map_smul,
      positive_fixes_reflection_value data degree cocycle equation positiveZero matrix positive, sub_self]
  · have negative : matrix.val.det < 0 := lt_of_le_of_ne (le_of_not_gt positive)
      (Matrix.GeneralLinearGroup.det_ne_zero matrix)
    have shiftedPositive : 0 < (matrix * reflection).val.det := by
      change 0 < (matrix * TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection).val.det
      simpa only [Units.val_mul, Matrix.det_mul, reflection_det, mul_neg_one] using neg_pos.mpr negative
    have productEquality : (matrix * reflection) * reflection = matrix := by
      rw [mul_assoc, TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes.reflection_mul_self, mul_one]
    have actionEquality := congrArg (fun operator : Module.End ℂ (Vectors data degree) => operator (cocycle reflection))
      (coefficientAction_mul data degree (matrix * reflection) reflection)
    rw [productEquality, Module.End.mul_apply, reflectionAction, map_neg,
      positive_fixes_reflection_value data degree cocycle equation positiveZero (matrix * reflection) shiftedPositive] at actionEquality
    have equality := equation matrix reflection
    rw [positiveZero _ shiftedPositive, actionEquality] at equality
    have valueEquality : cocycle matrix = cocycle reflection := by
      apply sub_eq_zero.mp
      simpa only [sub_eq_add_neg] using equality.symm
    rw [valueEquality, map_smul, actionEquality]
    module

theorem coboundary_of_differential_zero (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (zeroDifferential : hilbertDifferential data degree cocycle = 0) :
    ∃ vectors : Vectors data degree, ∀ matrix,
      cocycle matrix = coefficientAction data degree matrix vectors - vectors :=
  coboundary_of_positive_vanishing data degree cocycle equation
    (positive_cocycle_eq_zero data degree cocycle regularity equation zeroDifferential)

theorem differential_ne_zero (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (nontrivialClass : ¬ ∃ vectors : Vectors data degree, ∀ matrix,
      cocycle matrix = coefficientAction data degree matrix vectors - vectors) :
    hilbertDifferential data degree cocycle ≠ 0 := by
  intro zeroDifferential
  exact nontrivialClass (coboundary_of_differential_zero data degree cocycle regularity equation zeroDifferential)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroCocycleDifferential
