module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.AdelicTheta
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.SchwartzRegularization
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Theta.DistortionPoisson

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDecay TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFourierLinear

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachThetaPoisson

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]

def theta (realTest : SchwartzMap RealSpace Target) (finiteTest : FiniteRectangularFourier.Space → ℂ) (scale : ℝ) : Target :=
  ∑' matrix : Rectangular ℚ, finiteTest (coordinateHomeomorph (finiteMatrix matrix)) • realTest (scale • realVector matrix)

def pullback (realTest : SchwartzMap RealSpace Target) (transform : RealSpace ≃L[ℝ] RealSpace) : SchwartzMap RealSpace Target :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ transform realTest

theorem pullback_apply (realTest : SchwartzMap RealSpace Target) (transform : RealSpace ≃L[ℝ] RealSpace) (value : RealSpace) :
    pullback realTest transform value = realTest (transform value) := rfl

theorem summable_norm (realTest : SchwartzMap RealSpace Target) (finiteTest : FiniteRectangularFourier.Space → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest) (scale : ℝ) (nonzero : scale ≠ 0) :
    Summable (fun matrix : Rectangular ℚ => ‖finiteTest (coordinateHomeomorph (finiteMatrix matrix)) • realTest (scale • realVector matrix)‖) := by
  let finiteFunction := finiteTest ∘ coordinateHomeomorph
  have support : HasCompactSupport finiteFunction := finiteSupport.comp_homeomorph coordinateHomeomorph
  have continuous : Continuous finiteFunction := finiteContinuous.comp coordinateHomeomorph.continuous
  obtain ⟨bound, bounded⟩ := support.exists_bound_of_continuous continuous
  apply BanachRectangularSchwartz.summable_norm_of_bound (tsupport finiteFunction) support
    (BanachSchwartzRegularization.dilate realTest (Units.mk0 scale nonzero)) _ bound
  · intro matrix outside
    have zero : finiteFunction (finiteMatrix matrix) = 0 := by
      by_contra nonzero
      exact outside (subset_closure nonzero)
    change finiteFunction (finiteMatrix matrix) • _ = 0
    rw [zero, zero_smul]
  · intro matrix _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (bounded (finiteMatrix matrix)) (norm_nonneg _)

theorem summable [CompleteSpace Target] (realTest : SchwartzMap RealSpace Target) (finiteTest : FiniteRectangularFourier.Space → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest) (scale : ℝ) (nonzero : scale ≠ 0) :
    Summable (fun matrix : Rectangular ℚ => finiteTest (coordinateHomeomorph (finiteMatrix matrix)) • realTest (scale • realVector matrix)) :=
  (summable_norm realTest finiteTest finiteContinuous finiteSupport scale nonzero).of_norm

theorem theta_postcomp [CompleteSpace Target] (realTest : SchwartzMap RealSpace Target) (finiteTest : FiniteRectangularFourier.Space → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest) (scale : ℝ) (nonzero : scale ≠ 0)
    (functional : Target →L[ℂ] ℂ) :
    functional (theta realTest finiteTest scale) =
      AdelicThetaDecay.theta (SchwartzMap.postcompCLM functional realTest) finiteTest scale := by
  rw [theta, functional.map_tsum (summable realTest finiteTest finiteContinuous finiteSupport scale nonzero),
    ← AdelicThetaDecay.matrix_sum]
  apply tsum_congr
  intro matrix
  rw [map_smul, SchwartzMap.postcompCLM_apply, smul_eq_mul, mul_comm]

theorem postcomp_pullback (realTest : SchwartzMap RealSpace Target) (transform : RealSpace ≃L[ℝ] RealSpace)
    (functional : Target →L[ℂ] ℂ) :
    SchwartzMap.postcompCLM functional (pullback realTest transform) =
      AdelicThetaDistortion.pullback (SchwartzMap.postcompCLM functional realTest) transform := by
  ext value
  rfl

theorem fourier_postcomp [CompleteSpace Target] (realTest : SchwartzMap RealSpace Target) (functional : Target →L[ℂ] ℂ) :
    SchwartzMap.postcompCLM functional (FourierTransform.fourier realTest) =
      FourierTransform.fourier (SchwartzMap.postcompCLM functional realTest) := by
  ext frequency
  exact (BanachSchwartzPoisson.fourier_postcomp realTest functional frequency).symm

theorem poisson [CompleteSpace Target] (realTest : SchwartzMap RealSpace Target) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value)
    (transform : RealSpace ≃L[ℝ] RealSpace) (scale : ℝ) (positive : 0 < scale) :
    theta (pullback realTest transform) finiteTest scale = ((scale⁻¹ ^ 6 * factor transform : ℝ) : ℂ) •
      theta (pullback (FourierTransform.fourier realTest) (dual transform)) (FiniteRectangularFourier.transform finiteTest) scale⁻¹ := by
  have finiteContinuous := FiniteSchwartzClosure.continuous_of_periodic _ finiteTest finiteSupport invariant
  have transformContinuous := FiniteSchwartzClosure.transform_continuous _ finiteTest finiteSupport invariant
  have transformSupport := FiniteSchwartzClosure.transform_compactSupport _ finiteTest finiteSupport invariant
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro functional
  rw [map_smul, theta_postcomp _ _ finiteContinuous finiteSupport scale positive.ne',
    theta_postcomp _ _ transformContinuous transformSupport scale⁻¹ (inv_ne_zero positive.ne'),
    postcomp_pullback, postcomp_pullback, fourier_postcomp, smul_eq_mul]
  exact ThetaDistortionPoisson.poisson (SchwartzMap.postcompCLM functional realTest) latticeScale finiteTest
    finiteSupport invariant transform scale positive

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachThetaPoisson
