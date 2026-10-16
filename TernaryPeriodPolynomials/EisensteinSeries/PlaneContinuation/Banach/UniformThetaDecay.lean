module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.RationalUniformDecay
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.ThetaPoisson
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.FourierUniform

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDecay (coordinateHomeomorph)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDistortion (inverse_norm_bound)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFourierLinear TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachThetaPoisson

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachUniformThetaDecay

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target] [CompleteSpace Target]

theorem large (realTest : SchwartzMap RealSpace Target) (compact : Set FiniteRectangularFourier.Space)
    (compactIs : IsCompact compact) (bound : ℝ) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ finiteTest : FiniteRectangularFourier.Space → ℂ,
      (∀ value, value ∉ compact → finiteTest value = 0) → (∀ value, ‖finiteTest value‖ ≤ bound) →
      ∀ (transform : RealSpace ≃L[ℝ] RealSpace) (scale : ℝ), 1 ≤ scale →
        scale ^ power * ‖theta (pullback realTest transform) finiteTest scale - finiteTest 0 • realTest 0‖ ≤
          constant * ‖transform.symm.toContinuousLinearMap‖ ^ (power + Module.finrank ℤ integerLattice + 1) := by
  let matrixHull := coordinateHomeomorph.symm '' compact
  have matrixCompact : IsCompact matrixHull := compactIs.image coordinateHomeomorph.symm.continuous
  obtain ⟨constant, nonnegative, bounded⟩ := BanachRationalUniformDecay.uniform_remainder realTest matrixHull matrixCompact bound power
  refine ⟨constant, nonnegative, fun finiteTest finiteSupported finiteBound transform scale scaleLower => ?_⟩
  have matrixSupported : ∀ value, value ∉ matrixHull → (finiteTest ∘ coordinateHomeomorph) value = 0 := by
    intro value outside
    apply finiteSupported
    intro membership
    exact outside ⟨coordinateHomeomorph value, membership, coordinateHomeomorph.symm_apply_apply value⟩
  have result := bounded (finiteTest ∘ coordinateHomeomorph) matrixSupported (fun value => finiteBound _)
    transform.toContinuousLinearMap ‖transform.symm.toContinuousLinearMap‖ (norm_nonneg _)
    (inverse_norm_bound transform) scale scaleLower
  have zeroValue : coordinateHomeomorph 0 = 0 := rfl
  simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, theta, pullback_apply, map_smul, zeroValue] using result

theorem large_boxes (realTest : SchwartzMap RealSpace Target) (latticeScale : FiniteAdelesˣ)
    (offset : FiniteRectangularFourier.Space) (parameters : Set FiniteParameterThetaDecay.Parameter)
    (compact : IsCompact parameters) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter ∈ parameters,
      ∀ (transform : RealSpace ≃L[ℝ] RealSpace) (scale : ℝ), 1 ≤ scale →
        scale ^ power * ‖theta (pullback realTest transform) (FiniteFourierUniform.test latticeScale offset parameter) scale -
          FiniteFourierUniform.test latticeScale offset parameter 0 • realTest 0‖ ≤
            constant * ‖transform.symm.toContinuousLinearMap‖ ^ (power + Module.finrank ℤ integerLattice + 1) := by
  obtain ⟨hull, hullCompact, supported⟩ := FiniteFourierUniform.uniform_support latticeScale offset parameters compact
  obtain ⟨constant, nonnegative, bounded⟩ := large realTest hull hullCompact 1 power
  exact ⟨constant, nonnegative, fun parameter membership => bounded (FiniteFourierUniform.test latticeScale offset parameter)
    (supported parameter membership) (FiniteFourierUniform.test_norm latticeScale offset parameter)⟩

theorem small_boxes (realTest : SchwartzMap RealSpace Target) (latticeScale : FiniteAdelesˣ)
    (offset : FiniteRectangularFourier.Space) (parameters : Set FiniteParameterThetaDecay.Parameter)
    (compact : IsCompact parameters) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter ∈ parameters,
      ∀ (transform : RealSpace ≃L[ℝ] RealSpace) (scale : ℝ), 0 < scale → scale ≤ 1 →
        scale⁻¹ ^ power * ‖theta (pullback realTest transform) (FiniteFourierUniform.test latticeScale offset parameter) scale -
          ((scale⁻¹ ^ 6 * factor transform : ℝ) : ℂ) • (FiniteRectangularFourier.transform (FiniteFourierUniform.test latticeScale offset parameter) 0 •
            FourierTransform.fourier realTest 0)‖ ≤
          constant * factor transform * ‖transform.toContinuousLinearMap‖ ^ (power + 6 + Module.finrank ℤ integerLattice + 1) := by
  obtain ⟨rational, invariant⟩ := FiniteParameterLattices.box_uniform_periodic latticeScale offset parameters compact
  obtain ⟨hull, finiteBound, hullCompact, _, transformBound⟩ :=
    FiniteFourierUniform.uniform_transform latticeScale offset parameters compact
  obtain ⟨constant, nonnegative, bounded⟩ := large (FourierTransform.fourier realTest) hull hullCompact finiteBound (power + 6)
  refine ⟨constant, nonnegative, fun parameter membership transform scale positive upper => ?_⟩
  let finiteTest := FiniteFourierUniform.test latticeScale offset parameter
  have inverseLower : 1 ≤ scale⁻¹ := (one_le_inv₀ positive).mpr upper
  have bound := bounded (FiniteRectangularFourier.transform finiteTest)
    (transformBound parameter membership).1 (transformBound parameter membership).2 (dual transform) scale⁻¹ inverseLower
  rw [dual_inverse_norm] at bound
  rw [BanachThetaPoisson.poisson realTest rational finiteTest
    (FiniteFourierUniform.test_compactSupport latticeScale offset parameter) (invariant parameter membership) transform scale positive,
    ← smul_sub, norm_smul]
  have normFactor : ‖((scale⁻¹ ^ 6 * factor transform : ℝ) : ℂ)‖ = scale⁻¹ ^ 6 * factor transform := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr positive.le) _) (factor_positive transform).le)]
  rw [normFactor]
  calc
    _ = factor transform * (scale⁻¹ ^ (power + 6) *
        ‖theta (pullback (FourierTransform.fourier realTest) (dual transform))
          (FiniteRectangularFourier.transform finiteTest) scale⁻¹ -
          FiniteRectangularFourier.transform finiteTest 0 • FourierTransform.fourier realTest 0‖) := by rw [pow_add]; ring
    _ ≤ factor transform * (constant * ‖transform.toContinuousLinearMap‖ ^
        (power + 6 + Module.finrank ℤ integerLattice + 1)) :=
      mul_le_mul_of_nonneg_left bound (factor_positive transform).le
    _ = _ := by ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachUniformThetaDecay
