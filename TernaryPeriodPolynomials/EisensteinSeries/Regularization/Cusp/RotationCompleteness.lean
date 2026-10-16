module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationProjections

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspRotationProjection_inner (cusp : CuspidalRepresentation) (weight : ℤ) (vector test : cusp.H) :
    fourierCoeff (fun angle : AddCircle (1 : ℝ) => inner ℂ test (cuspCircularOrbit cusp vector angle)) weight =
      inner ℂ test (cuspRotationProjection cusp weight vector) := by
  have integrated := integral_inner (𝕜 := ℂ) (cuspRotationFourier_integrable cusp weight vector) test
  simpa only [fourierCoeff, smul_eq_mul, inner_smul_right, cuspRotationProjection_apply,
    cuspRotationFourier] using integrated

theorem cuspRotationProjection_complete (cusp : CuspidalRepresentation) (vector : cusp.H)
    (zero : ∀ weight, cuspRotationProjection cusp weight vector = 0) : vector = 0 := by
  let profile : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun angle => inner ℂ vector (cuspCircularOrbit cusp vector angle),
      continuous_const.inner (cuspCircularOrbit_continuous cusp vector)⟩
  have coefficients (weight : ℤ) : fourierCoeff profile weight = 0 := by
    change fourierCoeff (fun angle => inner ℂ vector (cuspCircularOrbit cusp vector angle)) weight = 0
    rw [cuspRotationProjection_inner, zero, inner_zero_right]
  have summable : Summable (fourierCoeff profile) := by
    simp only [show fourierCoeff profile = fun _ => 0 from funext coefficients]
    exact summable_zero
  have series := hasSum_fourier_series_of_summable (f := profile) summable
  have zero_series : HasSum (fun _ : ℤ => (0 : C(AddCircle (1 : ℝ), ℂ))) profile := by
    convert! series using 1
    funext weight
    rw [coefficients]
    exact (zero_smul ℂ (fourier weight : C(AddCircle (1 : ℝ), ℂ))).symm
  have zero_sum : HasSum (fun _ : ℤ => (0 : C(AddCircle (1 : ℝ), ℂ))) 0 := hasSum_zero
  have profile_zero : profile = 0 := zero_series.unique zero_sum
  have at_identity := congrArg (fun function : C(AddCircle (1 : ℝ), ℂ) => function 0) profile_zero
  change inner ℂ vector (cuspCircularOrbit cusp vector 0) = 0 at at_identity
  rw [cuspCircularOrbit_zero] at at_identity
  exact inner_self_eq_zero.mp at_identity

theorem cuspRotationProjection_exists_nonzero (cusp : CuspidalRepresentation) (vector : cusp.H) (nonzero : vector ≠ 0) :
    ∃ weight : ℤ, cuspRotationProjection cusp weight vector ≠ 0 := by
  by_contra failure
  push Not at failure
  exact nonzero (cuspRotationProjection_complete cusp vector failure)

theorem cuspRotationProjection_finite_fixed (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.H) (matrix : BinaryFiniteGL)
    (fixed : cusp.π (atFinite matrix) vector = vector) :
    cusp.π (atFinite matrix) (cuspRotationProjection cusp weight vector) = cuspRotationProjection cusp weight vector := by
  let action := (cuspUnitaryAction cusp (atFinite matrix)).toContinuousLinearMap
  change action (∫ angle : AddCircle (1 : ℝ), fourier (-weight) angle • cuspCircularOrbit cusp vector angle
    ∂AddCircle.haarAddCircle) = _
  rw [← action.integral_comp_comm (cuspRotationFourier_integrable cusp weight vector)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro angle
  dsimp only
  rw [map_smul action]
  congr 1
  change cusp.π (atFinite matrix) (cusp.π (atInfinity (binaryCircleRotation angle.toCircle)) vector) =
    cusp.π (atInfinity (binaryCircleRotation angle.toCircle)) vector
  rw [← Module.End.mul_apply, ← map_mul, ← binary_atInfinity_atFinite_commute, map_mul, Module.End.mul_apply, fixed]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
