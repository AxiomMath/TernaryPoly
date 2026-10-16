module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.PeriodizationFourier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section


open MeasureTheory UnitAddTorus
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzPeriodization TernaryPeriodPolynomials.PlaneEisensteinContinuation.TorusPeriodization
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PeriodizationFourier

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularPoisson

theorem character_fourierChar (frequency : Coordinate → ℤ) (vector : Coordinate → ℝ) :
    character frequency vector = (Real.fourierChar (-inner ℝ (WithLp.toLp 2 vector) (integerVector frequency)) : ℂ) := by
  simp only [character, mFourier, toTorus, ContinuousMap.coe_mk, fourier_coe_apply,
    Pi.neg_apply, Int.cast_neg, Complex.ofReal_one, div_one, Real.fourierChar_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [integerVector, EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply, star_trivial]
  push_cast
  simp only [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

theorem coefficient_fourier (function : SchwartzMap RealSpace ℂ) (frequency : Coordinate → ℤ) :
    mFourierCoeff (torusSum function) frequency = FourierTransform.fourier function (integerVector frequency) := by
  rw [coefficient_integral]
  have fourierEquality := congrFun (SchwartzMap.fourier_coe function) (integerVector frequency)
  rw [Real.fourier_eq] at fourierEquality
  rw [fourierEquality]
  calc
    (∫ vector : Coordinate → ℝ, weightedFunction function frequency vector) =
        ∫ vector : Coordinate → ℝ,
          Real.fourierChar (-inner ℝ (WithLp.toLp 2 vector) (integerVector frequency)) • function (WithLp.toLp 2 vector) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro vector
      change weightedFunction function frequency vector =
        Real.fourierChar (-inner ℝ (WithLp.toLp 2 vector) (integerVector frequency)) • function (WithLp.toLp 2 vector)
      rw [weightedFunction, character_fourierChar, coordinateFunction_apply]
      rfl
    _ = ∫ vector : RealSpace, Real.fourierChar (-inner ℝ vector (integerVector frequency)) • function vector :=
      (PiLp.volume_preserving_toLp Coordinate).integral_comp (MeasurableEquiv.toLp 2 (Coordinate → ℝ)).measurableEmbedding
        (fun vector : RealSpace => Real.fourierChar (-inner ℝ vector (integerVector frequency)) • function vector)

theorem coefficients_summable (function : SchwartzMap RealSpace ℂ) :
    Summable (mFourierCoeff (torusSum function)) := by
  have fourierSummable : Summable (fun frequency : Coordinate → ℤ => FourierTransform.fourier function (integerVector frequency)) := by
    simpa only [zero_add] using SchwartzPeriodization.summable (FourierTransform.fourier function) 0
  apply fourierSummable.congr
  intro frequency
  exact (coefficient_fourier function frequency).symm

theorem mFourier_origin (frequency : Coordinate → ℤ) : mFourier frequency (toTorus 0) = 1 := by
  simp [mFourier, toTorus]

theorem poisson_hasSum (function : SchwartzMap RealSpace ℂ) :
    HasSum (fun frequency : Coordinate → ℤ => FourierTransform.fourier function (integerVector frequency))
      (∑' integer : Coordinate → ℤ, function (integerVector integer)) := by
  have expansion := hasSum_mFourier_series_apply_of_summable
    (f := continuousSum function) (coefficients_summable function) (toTorus 0)
  simpa only [continuousSum, ContinuousMap.coe_mk, coefficient_fourier, mFourier_origin,
    smul_eq_mul, mul_one, torusSum_apply, periodization, zero_add] using expansion

theorem poisson (function : SchwartzMap RealSpace ℂ) :
    (∑' integer : Coordinate → ℤ, function (integerVector integer)) =
      ∑' frequency : Coordinate → ℤ, FourierTransform.fourier function (integerVector frequency) :=
  (poisson_hasSum function).tsum_eq.symm

theorem shifted_hasSum (function : SchwartzMap RealSpace ℂ) (offset : RealSpace) :
    HasSum (fun frequency : Coordinate → ℤ =>
      FourierTransform.fourier function (integerVector frequency) * mFourier frequency (toTorus offset))
      (∑' integer : Coordinate → ℤ, function (offset + integerVector integer)) := by
  have expansion := hasSum_mFourier_series_apply_of_summable
    (f := continuousSum function) (coefficients_summable function) (toTorus offset)
  simpa only [continuousSum, ContinuousMap.coe_mk, coefficient_fourier,
    smul_eq_mul, torusSum_apply, periodization] using expansion

theorem shifted_poisson (function : SchwartzMap RealSpace ℂ) (offset : RealSpace) :
    (∑' integer : Coordinate → ℤ, function (offset + integerVector integer)) =
      ∑' frequency : Coordinate → ℤ,
        FourierTransform.fourier function (integerVector frequency) * mFourier frequency (toTorus offset) :=
  (shifted_hasSum function offset).tsum_eq.symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularPoisson
