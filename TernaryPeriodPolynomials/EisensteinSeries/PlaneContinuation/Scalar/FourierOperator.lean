module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FourierUniqueness

@[expose] public section


open MeasureTheory TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarFourierOperator

theorem norm_fourierCoeff_le (function : C(Parameter, ℂ)) (index : ℤ) :
    ‖fourierCoeff function index‖ ≤ ‖function‖ := by
  have estimate := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (Filter.Eventually.of_forall (fun point : Parameter => show
      ‖fourier (-index) point • function point‖ ≤ ‖function‖ by
        rw [norm_smul, fourier_norm_one, one_mul]
        exact function.norm_coe_le_norm point))
  simpa [fourierCoeff] using estimate

noncomputable def coefficientOperator (index : ℤ) : C(Parameter, ℂ) →L[ℂ] ℂ :=
  let linear : C(Parameter, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun function => fourierCoeff function index
      map_add' := fun first second => congrFun (fourierCoeff.add
        (first.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (second.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))) index
      map_smul' := fun scalar function => fourierCoeff.const_smul function scalar index }
  linear.mkContinuous 1 (fun function => by
    change ‖fourierCoeff function index‖ ≤ 1 * ‖function‖
    simpa only [one_mul] using norm_fourierCoeff_le function index)

theorem coefficientOperator_apply (index : ℤ) (function : C(Parameter, ℂ)) :
    coefficientOperator index function = fourierCoeff function index := rfl

theorem coefficientOperator_norm_le (index : ℤ) : ‖coefficientOperator index‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro function
  change ‖fourierCoeff function index‖ ≤ 1 * ‖function‖
  simpa only [one_mul] using norm_fourierCoeff_le function index

theorem fourierCoeff_translate (function : Parameter → ℂ) (parameter : Parameter) (index : ℤ) :
    fourierCoeff (fun point => function (parameter + point)) index =
      fourier index parameter * fourierCoeff function index := by
  unfold fourierCoeff
  calc
    _ = ∫ point : Parameter, fourier index parameter •
        (fourier (-index) (parameter + point) • function (parameter + point)) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun point => by
        change fourier (-index) point • function (parameter + point) =
          fourier index parameter • (fourier (-index) (parameter + point) • function (parameter + point))
        rw [smul_smul, fourier_add_argument, ← mul_assoc, fourier_mul_neg, one_mul])
    _ = fourier index parameter • (∫ point : Parameter,
        fourier (-index) (parameter + point) • function (parameter + point) ∂AddCircle.haarAddCircle) :=
      integral_smul _ _
    _ = _ := congrArg (fun value : ℂ => fourier index parameter * value)
      (integral_add_left_eq_self (fun point : Parameter => fourier (-index) point • function point) parameter)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarFourierOperator
