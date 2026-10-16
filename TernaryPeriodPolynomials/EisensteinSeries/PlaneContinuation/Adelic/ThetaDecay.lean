module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.SchwartzClosure

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDecay

def coordinateHomeomorph : Rectangular FiniteAdeles ≃ₜ FiniteRectangularFourier.Space where
  toEquiv := RectangularAdelicPoisson.coordinates.toEquiv
  continuous_toFun := continuous_pi (fun coordinate => (continuous_apply coordinate.2).comp (continuous_apply coordinate.1))
  continuous_invFun := continuous_pi (fun row => continuous_pi (fun column => continuous_apply (row, column)))

def theta (realTest : SchwartzMap RealSpace ℂ) (finiteTest : FiniteRectangularFourier.Space → ℂ) (scale : ℝ) : ℂ :=
  ∑' rational : Coordinate → ℚ, realTest (scale • (UnitBoxPoisson.rationalPoint rational).1) *
    finiteTest (UnitBoxPoisson.rationalPoint rational).2

theorem matrix_sum (realTest : SchwartzMap RealSpace ℂ) (finiteTest : FiniteRectangularFourier.Space → ℂ) (scale : ℝ) :
    (∑' matrix : Rectangular ℚ, realTest (scale • realVector matrix) * finiteTest (coordinateHomeomorph (finiteMatrix matrix))) =
      theta realTest finiteTest scale :=
  (RectangularAdelicPoisson.coordinates (Ring := ℚ)).toEquiv.tsum_eq
    (fun rational => realTest (scale • (UnitBoxPoisson.rationalPoint rational).1) * finiteTest (UnitBoxPoisson.rationalPoint rational).2)

theorem rapid_large (realTest : SchwartzMap RealSpace ℂ) (finiteTest : FiniteRectangularFourier.Space → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ scale : ℝ, 1 ≤ scale →
      scale ^ power * ‖theta realTest finiteTest scale - realTest 0 * finiteTest 0‖ ≤ constant := by
  obtain ⟨constant, nonnegative, bound⟩ := RationalThetaDecay.rapid_remainder realTest (finiteTest ∘ coordinateHomeomorph)
    (finiteContinuous.comp coordinateHomeomorph.continuous) (finiteSupport.comp_homeomorph coordinateHomeomorph) power
  refine ⟨constant, nonnegative, fun scale scaleLower => ?_⟩
  have equality : coordinateHomeomorph 0 = 0 := rfl
  simpa only [Function.comp_apply, matrix_sum, equality] using bound scale scaleLower

theorem poisson (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value) (scale : ℝ) (positive : 0 < scale) :
    theta realTest finiteTest scale = ((scale⁻¹ ^ 6 : ℝ) : ℂ) *
      theta (FourierTransform.fourier realTest) (FiniteRectangularFourier.transform finiteTest) scale⁻¹ := by
  let unit := Units.mk0 scale positive.ne'
  have equality := ThetaScalingPoisson.poisson realTest latticeScale finiteTest finiteSupport invariant unit
  have factor : RealFourierScaling.factor unit = scale⁻¹ ^ 6 := RealFourierScaling.factor_of_positive unit positive
  rw [factor] at equality
  exact equality

theorem rapid_small (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ scale : ℝ, 0 < scale → scale ≤ 1 →
      scale⁻¹ ^ power * ‖theta realTest finiteTest scale - ((scale⁻¹ ^ 6 : ℝ) : ℂ) *
        (FourierTransform.fourier realTest 0 * FiniteRectangularFourier.transform finiteTest 0)‖ ≤ constant := by
  obtain ⟨constant, nonnegative, bound⟩ := rapid_large (FourierTransform.fourier realTest) (FiniteRectangularFourier.transform finiteTest)
    (FiniteSchwartzClosure.transform_continuous (FiniteLatticeMeasure.rationalScale latticeScale) finiteTest finiteSupport invariant)
    (FiniteSchwartzClosure.transform_compactSupport (FiniteLatticeMeasure.rationalScale latticeScale) finiteTest finiteSupport invariant)
    (power + 6)
  refine ⟨constant, nonnegative, fun scale positive upper => ?_⟩
  have inverseLower : 1 ≤ scale⁻¹ := (one_le_inv₀ positive).mpr upper
  have bounded := bound scale⁻¹ inverseLower
  rw [poisson realTest latticeScale finiteTest finiteSupport invariant scale positive, ← mul_sub, norm_mul]
  have normFactor : ‖((scale⁻¹ ^ 6 : ℝ) : ℂ)‖ = scale⁻¹ ^ 6 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr positive.le) _)]
  rw [normFactor, ← mul_assoc, ← pow_add]
  exact bounded

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDecay
