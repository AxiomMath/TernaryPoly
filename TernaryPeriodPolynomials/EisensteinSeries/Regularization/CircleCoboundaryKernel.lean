module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ContinuousFourierSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def circleCoboundaryCoefficient (weight : ℤ) (angle : AddCircle (1 : ℝ))
    (order : ℕ) (index : ℤ) : ℂ :=
  ((fourier (-index) angle - fourier weight angle) *
    (Complex.I * ((-index - weight : ℤ) : ℂ)) ^ order)⁻¹

noncomputable def circleCoboundaryKernel (weight : ℤ) (angle : AddCircle (1 : ℝ))
    (order : ℕ) : C(AddCircle (1 : ℝ), ℂ) :=
  continuousFourierSeries (circleCoboundaryCoefficient weight angle order)

theorem circleCoboundaryKernel_coefficient (weight : ℤ) (angle : AddCircle (1 : ℝ)) (order : ℕ)
    (nonresonant : ∀ other : ℤ, other ≠ weight → fourier other angle ≠ fourier weight angle)
    (summable : Summable (fun index => ‖circleCoboundaryCoefficient weight angle order index‖))
    (other : ℤ) :
    (fourier other angle - fourier weight angle) * fourierCoeff (circleCoboundaryKernel weight angle order) (-other) *
      (Complex.I * ((other - weight : ℤ) : ℂ)) ^ order = if other = weight then 0 else 1 := by
  by_cases equal : other = weight
  · subst other
    simp
  · rw [ite_eq_right equal]
    have phase_nonzero : fourier other angle - fourier weight angle ≠ 0 := sub_ne_zero.mpr (nonresonant other equal)
    have integer_nonzero : ((other - weight : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr equal)
    have derivative_nonzero : (Complex.I * ((other - weight : ℤ) : ℂ)) ^ order ≠ 0 :=
      pow_ne_zero order (mul_ne_zero Complex.I_ne_zero integer_nonzero)
    change (fourier other angle - fourier weight angle) *
      fourierCoeff (continuousFourierSeries (circleCoboundaryCoefficient weight angle order)) (-other) * _ = 1
    rw [continuousFourierSeries_coefficient _ summable, circleCoboundaryCoefficient, neg_neg]
    calc
      _ = ((fourier other angle - fourier weight angle) * (Complex.I * ((other - weight : ℤ) : ℂ)) ^ order) *
          ((fourier other angle - fourier weight angle) * (Complex.I * ((other - weight : ℤ) : ℂ)) ^ order)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ (mul_ne_zero phase_nonzero derivative_nonzero)

theorem cusp_realize_projection_of_summable_inverse (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (weight : ℤ) (angle : AddCircle (1 : ℝ)) (order : ℕ)
    (nonresonant : ∀ other : ℤ, other ≠ weight → fourier other angle ≠ fourier weight angle)
    (summable : Summable (fun index => ‖circleCoboundaryCoefficient weight angle order index‖))
    (vector : cusp.smooth) :
    cusp.realize (cuspSmoothRotationProjection cusp weight vector) argument =
      fourierCoeff (cuspScalarCircleOrbit cusp argument vector) weight :=
  cusp_realize_projection_of_kernel cusp argument weight angle order (circleCoboundaryKernel weight angle order)
    (circleCoboundaryKernel_coefficient weight angle order nonresonant summable) vector

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
