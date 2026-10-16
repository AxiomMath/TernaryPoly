module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rational.DistortionDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDistortion

def pullback (realTest : SchwartzMap RealSpace ℂ) (transform : RealSpace ≃L[ℝ] RealSpace) : SchwartzMap RealSpace ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ transform realTest

theorem pullback_apply (realTest : SchwartzMap RealSpace ℂ) (transform : RealSpace ≃L[ℝ] RealSpace) (value : RealSpace) :
    pullback realTest transform value = realTest (transform value) := rfl

theorem matrix_sum (realTest : SchwartzMap RealSpace ℂ) (finiteTest : FiniteRectangularFourier.Space → ℂ)
    (transform : RealSpace ≃L[ℝ] RealSpace) (scale : ℝ) :
    (∑' matrix : Rectangular ℚ,
      realTest (scale • transform (realVector matrix)) * finiteTest (coordinateHomeomorph (finiteMatrix matrix))) =
        theta (pullback realTest transform) finiteTest scale := by
  rw [← AdelicThetaDecay.matrix_sum]
  apply tsum_congr
  intro matrix
  rw [pullback_apply, transform.map_smul]

theorem rapid_large (realTest : SchwartzMap RealSpace ℂ) (finiteTest : FiniteRectangularFourier.Space → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (transform : RealSpace ≃L[ℝ] RealSpace) (distortion : ℝ), 0 ≤ distortion →
        (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) → ∀ scale : ℝ, 1 ≤ scale →
          scale ^ power * ‖theta (pullback realTest transform) finiteTest scale - realTest 0 * finiteTest 0‖ ≤
            constant * distortion ^ (power + Module.finrank ℤ integerLattice + 1) := by
  obtain ⟨constant, nonnegative, bound⟩ := RationalDistortionDecay.rapid_remainder realTest (finiteTest ∘ coordinateHomeomorph)
    (finiteContinuous.comp coordinateHomeomorph.continuous) (finiteSupport.comp_homeomorph coordinateHomeomorph) power
  refine ⟨constant, nonnegative, fun transform distortion distortionNonnegative distortionBound scale scaleLower => ?_⟩
  have equality : coordinateHomeomorph 0 = 0 := rfl
  simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, matrix_sum, equality] using
    bound transform.toContinuousLinearMap distortion distortionNonnegative distortionBound scale scaleLower

theorem inverse_norm_bound (transform : RealSpace ≃L[ℝ] RealSpace) (vector : RealSpace) :
    ‖vector‖ ≤ ‖transform.symm.toContinuousLinearMap‖ * ‖transform vector‖ := by
  simpa only [ContinuousLinearEquiv.coe_coe, transform.symm_apply_apply] using
    transform.symm.toContinuousLinearMap.le_opNorm (transform vector)

theorem rapid_large_opNorm (realTest : SchwartzMap RealSpace ℂ) (finiteTest : FiniteRectangularFourier.Space → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (transform : RealSpace ≃L[ℝ] RealSpace) (scale : ℝ), 1 ≤ scale →
      scale ^ power * ‖theta (pullback realTest transform) finiteTest scale - realTest 0 * finiteTest 0‖ ≤
        constant * ‖transform.symm.toContinuousLinearMap‖ ^ (power + Module.finrank ℤ integerLattice + 1) := by
  obtain ⟨constant, nonnegative, bound⟩ := rapid_large realTest finiteTest finiteContinuous finiteSupport power
  exact ⟨constant, nonnegative, fun transform scale scaleLower =>
    bound transform _ (norm_nonneg _) (inverse_norm_bound transform) scale scaleLower⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDistortion
