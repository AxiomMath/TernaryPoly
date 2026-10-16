module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.Poisson

@[expose] public section


open MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzPeriodization

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzPoisson

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target] [CompleteSpace Target]

omit [CompleteSpace Target] in
theorem summable_norm_lattice {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] (lattice : Submodule ℤ Space) [DiscreteTopology lattice]
    (function : SchwartzMap Space Target) : Summable (fun point : lattice => ‖function point.val‖) := by
  classical
  let order := Module.finrank ℤ lattice + 1
  obtain ⟨bound, positive, decay⟩ := function.decay order 0
  simp only [norm_iteratedFDeriv_zero] at decay
  have summableDecay : Summable (fun point : lattice => bound * ‖point‖⁻¹ ^ order) :=
    (ZLattice.summable_norm_pow_inv lattice order (Nat.lt_succ_self _)).mul_left bound
  have summableZero : Summable (fun point : lattice => if point = 0 then ‖function 0‖ else 0) :=
    (hasSum_ite_eq (0 : lattice) ‖function 0‖).summable
  apply (summableZero.add summableDecay).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro point
  by_cases zeroPoint : point = 0
  · subst point
    simp only [ite_true, ZeroMemClass.coe_zero, norm_zero, inv_zero]
    exact le_add_of_nonneg_right (mul_nonneg positive.le (pow_nonneg (by positivity) _))
  · have normPositive : 0 < ‖point.val‖ := norm_pos_iff.mpr (fun zero => zeroPoint (Subtype.ext zero))
    simp only [ite_eq_right zeroPoint, zero_add]
    change ‖function point.val‖ ≤ bound * ‖point.val‖⁻¹ ^ order
    rw [inv_pow, ← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos normPositive order)).mpr (by simpa only [mul_comm] using decay point.val)

omit [CompleteSpace Target] in
theorem summable_norm_integer (function : SchwartzMap RealSpace Target) :
    Summable (fun integer : Coordinate → ℤ => ‖function (integerVector integer)‖) := by
  have latticeSummable : Summable (fun point : integerLattice => ‖function point.val‖) :=
    summable_norm_lattice integerLattice function
  have result : Summable (fun integer : Coordinate → ℤ => ‖function (latticeVector integer).val‖) :=
    latticeSummable.comp_injective latticeVector_injective
  exact result

theorem summable_integer (function : SchwartzMap RealSpace Target) :
    Summable (fun integer : Coordinate → ℤ => function (integerVector integer)) :=
  (summable_norm_integer function).of_norm

omit [CompleteSpace Target] in
theorem fourier_integral (function : SchwartzMap RealSpace Target) (frequency : RealSpace) :
    FourierTransform.fourier function frequency =
      ∫ value, (Real.fourierChar (-inner ℝ value frequency) : ℂ) • function value := by
  have equality := congrFun (SchwartzMap.fourier_coe function) frequency
  rw [Real.fourier_eq] at equality
  exact equality

omit [CompleteSpace Target] in
theorem fourier_integrand_integrable (function : SchwartzMap RealSpace Target) (frequency : RealSpace) :
    Integrable (fun value => (Real.fourierChar (-inner ℝ value frequency) : ℂ) • function value) := by
  have continuousWeight : Continuous (fun value : RealSpace => (Real.fourierChar (-inner ℝ value frequency) : ℂ)) := by
    fun_prop
  apply function.integrable.norm.mono' (continuousWeight.smul function.continuous).aestronglyMeasurable
  filter_upwards [] with value
  change ‖(Real.fourierChar (-inner ℝ value frequency) : ℂ) • function value‖ ≤ ‖function value‖
  rw [norm_smul]
  exact (congrArg (fun norm : ℝ => norm * ‖function value‖)
    (Circle.norm_coe (Real.fourierChar (-inner ℝ value frequency)))).trans_le (by simp)

theorem fourier_postcomp (function : SchwartzMap RealSpace Target) (functional : Target →L[ℂ] ℂ)
    (frequency : RealSpace) :
    FourierTransform.fourier (SchwartzMap.postcompCLM functional function) frequency =
      functional (FourierTransform.fourier function frequency) := by
  rw [fourier_integral, fourier_integral, ← functional.integral_comp_comm (fourier_integrand_integrable function frequency)]
  apply integral_congr_ae
  filter_upwards [] with value
  simp only [SchwartzMap.postcompCLM_apply, map_smul]

theorem poisson (function : SchwartzMap RealSpace Target) :
    (∑' integer : Coordinate → ℤ, function (integerVector integer)) =
      ∑' frequency : Coordinate → ℤ, FourierTransform.fourier function (integerVector frequency) := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro functional
  rw [functional.map_tsum (summable_integer function),
    functional.map_tsum (summable_integer (FourierTransform.fourier function))]
  have scalar := RectangularPoisson.poisson (SchwartzMap.postcompCLM functional function)
  simpa only [SchwartzMap.postcompCLM_apply, fourier_postcomp] using scalar

theorem poisson_hasSum (function : SchwartzMap RealSpace Target) :
    HasSum (fun frequency : Coordinate → ℤ => FourierTransform.fourier function (integerVector frequency))
      (∑' integer : Coordinate → ℤ, function (integerVector integer)) := by
  rw [poisson]
  exact (summable_integer (FourierTransform.fourier function)).hasSum

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzPoisson
