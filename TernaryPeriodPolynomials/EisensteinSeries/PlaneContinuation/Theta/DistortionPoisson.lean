module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.FourierLinear

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDecay
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDistortion TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFourierLinear

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaDistortionPoisson

theorem theta_smul (realTest : SchwartzMap RealSpace ℂ) (finiteTest : FiniteRectangularFourier.Space → ℂ)
    (scalar : ℝ) (scale : ℝ) :
    theta (scalar • realTest) finiteTest scale = (scalar : ℂ) * theta realTest finiteTest scale := by
  simp only [theta, smul_apply, Complex.real_smul, mul_assoc, tsum_mul_left]

theorem poisson (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value)
    (transform : RealSpace ≃L[ℝ] RealSpace) (scale : ℝ) (positive : 0 < scale) :
    theta (pullback realTest transform) finiteTest scale = ((scale⁻¹ ^ 6 * factor transform : ℝ) : ℂ) *
      theta (pullback (FourierTransform.fourier realTest) (dual transform)) (FiniteRectangularFourier.transform finiteTest) scale⁻¹ := by
  rw [AdelicThetaDecay.poisson (pullback realTest transform) latticeScale finiteTest finiteSupport invariant scale positive,
    fourier_pullback_eq, theta_smul, Complex.ofReal_mul, mul_assoc]

theorem rapid_small (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (transform : RealSpace ≃L[ℝ] RealSpace) (scale : ℝ), 0 < scale → scale ≤ 1 →
      scale⁻¹ ^ power * ‖theta (pullback realTest transform) finiteTest scale -
        ((scale⁻¹ ^ 6 * factor transform : ℝ) : ℂ) *
          (FourierTransform.fourier realTest 0 * FiniteRectangularFourier.transform finiteTest 0)‖ ≤
        constant * factor transform * ‖transform.toContinuousLinearMap‖ ^ (power + 6 + Module.finrank ℤ integerLattice + 1) := by
  obtain ⟨constant, nonnegative, bound⟩ := AdelicThetaDistortion.rapid_large_opNorm
    (FourierTransform.fourier realTest) (FiniteRectangularFourier.transform finiteTest)
    (FiniteSchwartzClosure.transform_continuous _ finiteTest finiteSupport invariant)
    (FiniteSchwartzClosure.transform_compactSupport _ finiteTest finiteSupport invariant) (power + 6)
  refine ⟨constant, nonnegative, fun transform scale positive upper => ?_⟩
  have inverseLower : 1 ≤ scale⁻¹ := (one_le_inv₀ positive).mpr upper
  have bounded := bound (dual transform) scale⁻¹ inverseLower
  rw [dual_inverse_norm] at bounded
  rw [poisson realTest latticeScale finiteTest finiteSupport invariant transform scale positive, ← mul_sub, norm_mul]
  have normFactor : ‖((scale⁻¹ ^ 6 * factor transform : ℝ) : ℂ)‖ = scale⁻¹ ^ 6 * factor transform := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr positive.le) _) (factor_positive transform).le)]
  rw [normFactor]
  calc
    _ = factor transform * (scale⁻¹ ^ (power + 6) *
        ‖theta (pullback (FourierTransform.fourier realTest) (dual transform))
          (FiniteRectangularFourier.transform finiteTest) scale⁻¹ -
          FourierTransform.fourier realTest 0 * FiniteRectangularFourier.transform finiteTest 0‖) := by rw [pow_add]; ring
    _ ≤ factor transform * (constant * ‖transform.toContinuousLinearMap‖ ^
        (power + 6 + Module.finrank ℤ integerLattice + 1)) :=
      mul_le_mul_of_nonneg_left bounded (factor_positive transform).le
    _ = _ := by ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaDistortionPoisson
