module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.FourierScaling

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRectangularFourier

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaScalingPoisson

theorem poisson_hasSum (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (compactSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value) (scale : ℝˣ) :
    HasSum (fun rational : Coordinate → ℚ =>
      (RealFourierScaling.factor scale : ℂ) *
        FourierTransform.fourier realTest (scale.inv • (UnitBoxPoisson.rationalPoint rational).1) *
        FiniteRectangularFourier.transform finiteTest (UnitBoxPoisson.rationalPoint rational).2)
      (∑' rational : Coordinate → ℚ,
        realTest (scale.val • (UnitBoxPoisson.rationalPoint rational).1) *
          finiteTest (UnitBoxPoisson.rationalPoint rational).2) := by
  have result := FiniteLatticeCosets.poisson_hasSum (RealFourierScaling.dilate realTest scale)
    latticeScale finiteTest compactSupport invariant
  simpa only [transform_tensor, RealFourierScaling.fourier_dilate, tensor,
    RealFourierScaling.dilate_apply, Complex.real_smul] using result

theorem poisson (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (compactSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value) (scale : ℝˣ) :
    (∑' rational : Coordinate → ℚ,
      realTest (scale.val • (UnitBoxPoisson.rationalPoint rational).1) *
        finiteTest (UnitBoxPoisson.rationalPoint rational).2) =
      (RealFourierScaling.factor scale : ℂ) * ∑' rational : Coordinate → ℚ,
        FourierTransform.fourier realTest (scale.inv • (UnitBoxPoisson.rationalPoint rational).1) *
          FiniteRectangularFourier.transform finiteTest (UnitBoxPoisson.rationalPoint rational).2 := by
  rw [← tsum_mul_left]
  simpa only [mul_assoc] using (poisson_hasSum realTest latticeScale finiteTest compactSupport invariant scale).tsum_eq.symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaScalingPoisson
