module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Lie.Differentiation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierDifferentiation

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationInfinitesimal

theorem derivative_of_eigen (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (eigen : ∀ parameter : Parameter, data.π (atInfinity (rotation parameter)) vector.val =
      fourier index parameter • vector.val) :
    rotationDerivative data vector = frequency index • vector := by
  have derivative := orbit_hasDerivAt data vector 0
  have curveEquality : (fun time : ℝ => data.π (atInfinity (rotation (time : Parameter))) vector.val) =
      (fun time : ℝ => fourier index (time : Parameter) • vector.val) := funext (fun time => eigen (time : Parameter))
  rw [curveEquality] at derivative
  have comparison := (fourier_hasDerivAt index 0).smul_const vector.val
  have equality := derivative.unique comparison
  apply Subtype.ext
  change (rotationDerivative data vector).val = frequency index • vector.val
  simpa only [AddCircle.coe_zero, rotation_zero, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one,
    map_one, Module.End.one_apply, fourier_eval_zero, mul_one] using equality

theorem eigen_of_derivative (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (eigenDerivative : rotationDerivative data vector = frequency index • vector) :
    ∀ parameter : Parameter, data.π (atInfinity (rotation parameter)) vector.val =
      fourier index parameter • vector.val := by
  have derivativeValue : (rotationDerivative data vector).val = frequency index • vector.val :=
    congrArg Subtype.val eigenDerivative
  have derivativeZero (time : ℝ) : HasDerivAt (fun time : ℝ =>
      fourier (-index) (time : Parameter) • data.π (atInfinity (rotation (time : Parameter))) vector.val) 0 time := by
    have derivative := (fourier_hasDerivAt (-index) time).smul (orbit_hasDerivAt data vector time)
    rw [derivativeValue, map_smul, frequency_neg] at derivative
    have cancellation : fourier (-index) (time : Parameter) •
        (frequency index • data.π (atInfinity (rotation (time : Parameter))) vector.val) +
      (-frequency index * fourier (-index) (time : Parameter)) •
        data.π (atInfinity (rotation (time : Parameter))) vector.val = 0 := by
      rw [smul_smul, neg_mul, neg_smul, mul_comm (fourier (-index) (time : Parameter)), add_neg_cancel]
    exact derivative.congr_deriv cancellation
  have constant := is_const_of_deriv_eq_zero
    (fun time => (derivativeZero time).differentiableAt) (fun time => (derivativeZero time).deriv)
  intro parameter
  obtain ⟨time, timeEquality⟩ := QuotientAddGroup.mk_surjective parameter
  subst parameter
  have identity := constant time 0
  simp only [AddCircle.coe_zero, rotation_zero, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one,
    map_one, Module.End.one_apply, fourier_eval_zero, one_smul] at identity
  have multiplied := congrArg (fun value : data.H => fourier index (time : Parameter) • value) identity
  rw [smul_smul, fourier_mul_neg, one_smul] at multiplied
  exact multiplied

theorem derivative_eigen_iff (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ) :
    rotationDerivative data vector = frequency index • vector ↔
      ∀ parameter : Parameter, data.π (atInfinity (rotation parameter)) vector.val =
        fourier index parameter • vector.val :=
  ⟨eigen_of_derivative data vector index, derivative_of_eigen data vector index⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationInfinitesimal
