module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.CircleCoboundaryKernel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem circle_fourier_sub_factor (first second : ℤ) (angle : AddCircle (1 : ℝ)) :
    fourier first angle - fourier second angle =
      fourier second angle * (fourier (first - second) angle - 1) := by
  rw [mul_sub, mul_one, ← fourier_add, show second + (first - second) = first by omega]

theorem circle_fourier_sub_inverse_norm (first second : ℤ) (angle : AddCircle (1 : ℝ)) :
    ‖(fourier first angle - fourier second angle)⁻¹‖ = ‖(fourier (first - second) angle - 1)⁻¹‖ := by
  rw [circle_fourier_sub_factor, norm_inv, norm_mul, circle_fourier_norm, one_mul, norm_inv]

theorem circleCoboundaryCoefficient_norm_bound (weight : ℤ) (angle : AddCircle (1 : ℝ)) (constant : ℝ)
    (bound : ∀ integer : ℤ, integer ≠ 0 →
      ‖(fourier integer angle - 1)⁻¹‖ ≤ constant * |(integer : ℝ)| ^ 2) (index : ℤ) :
    ‖circleCoboundaryCoefficient weight angle 4 index‖ ≤
      constant * (1 / |((-index - weight : ℤ) : ℝ)| ^ 2) := by
  by_cases zero : -index - weight = 0
  · have equal : -index = weight := by omega
    simp [circleCoboundaryCoefficient, equal]
  · have nonzero : |((-index - weight : ℤ) : ℝ)| ≠ 0 :=
      abs_ne_zero.mpr (by exact_mod_cast zero)
    have norm_value : ‖circleCoboundaryCoefficient weight angle 4 index‖ =
        ‖(fourier (-index) angle - fourier weight angle)⁻¹‖ *
          (|((-index - weight : ℤ) : ℝ)| ^ 4)⁻¹ := by
      simp only [circleCoboundaryCoefficient, norm_inv, norm_mul, norm_pow,
        Complex.norm_I, Complex.norm_intCast, mul_one, mul_inv_rev, mul_comm]
    rw [norm_value, circle_fourier_sub_inverse_norm]
    calc
      _ ≤ (constant * |((-index - weight : ℤ) : ℝ)| ^ 2) *
          (|((-index - weight : ℤ) : ℝ)| ^ 4)⁻¹ :=
        mul_le_mul_of_nonneg_right (bound (-index - weight) zero) (by positivity)
      _ = _ := by field_simp

theorem circleCoboundaryCoefficient_summable_of_bound (weight : ℤ) (angle : AddCircle (1 : ℝ))
    (constant : ℝ) (bound : ∀ integer : ℤ, integer ≠ 0 →
      ‖(fourier integer angle - 1)⁻¹‖ ≤ constant * |(integer : ℝ)| ^ 2) :
    Summable (fun index => ‖circleCoboundaryCoefficient weight angle 4 index‖) := by
  have reindexed := ((Equiv.neg ℤ).trans (Equiv.subRight weight)).summable_iff.mpr integer_inverse_square_summable
  have inverse_squares : Summable (fun index : ℤ => 1 / |((-index - weight : ℤ) : ℝ)| ^ 2) := by
    convert! reindexed using 1
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (circleCoboundaryCoefficient_norm_bound weight angle constant bound) (inverse_squares.mul_left constant)

theorem cusp_realize_projection_of_small_divisor_bound (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (weight : ℤ) (angle : AddCircle (1 : ℝ))
    (nonresonant : ∀ integer : ℤ, integer ≠ 0 → fourier integer angle ≠ 1)
    (constant : ℝ) (bound : ∀ integer : ℤ, integer ≠ 0 →
      ‖(fourier integer angle - 1)⁻¹‖ ≤ constant * |(integer : ℝ)| ^ 2)
    (vector : cusp.smooth) :
    cusp.realize (cuspSmoothRotationProjection cusp weight vector) argument =
      fourierCoeff (cuspScalarCircleOrbit cusp argument vector) weight := by
  apply cusp_realize_projection_of_summable_inverse cusp argument weight angle 4 _
    (circleCoboundaryCoefficient_summable_of_bound weight angle constant bound) vector
  intro other distinct equal
  have product : fourier weight angle * (fourier (other - weight) angle - 1) = 0 := by
    rw [← circle_fourier_sub_factor, equal, sub_self]
  have phase_nonzero : fourier weight angle ≠ 0 := by
    intro zero
    have norm := circle_fourier_norm weight angle
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm
  exact nonresonant (other - weight) (sub_ne_zero.mpr distinct)
    (sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left phase_nonzero))

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
