module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.RationalUniformDecay
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.AbsoluteTheta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachRationalUniformDecay TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteParameterThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachAbsoluteTheta

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]

def absoluteTail (realTest : SchwartzMap RealSpace Target) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (parameter : Parameter) (transform : RealSpace →L[ℝ] RealSpace) (scale : ℝ) : ℝ :=
  ∑' matrix, ‖tailTerm realTest (FiniteParameterThetaDecay.pullback finiteTest parameter) transform scale matrix‖

theorem tail_nonnegative (realTest : SchwartzMap RealSpace Target) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (parameter : Parameter) (transform : RealSpace →L[ℝ] RealSpace) (scale : ℝ) :
    0 ≤ absoluteTail realTest finiteTest parameter transform scale := tsum_nonneg (fun _ => norm_nonneg _)

theorem uniform_large (realTest : SchwartzMap RealSpace Target) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameters : Set Parameter) (compact : IsCompact parameters) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter ∈ parameters,
      ∀ (transform : RealSpace →L[ℝ] RealSpace) (distortion : ℝ), 0 ≤ distortion →
        (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) → ∀ scale : ℝ, 1 ≤ scale →
          Summable (fun matrix => ‖tailTerm realTest (FiniteParameterThetaDecay.pullback finiteTest parameter) transform scale matrix‖) ∧
          scale ^ power * absoluteTail realTest finiteTest parameter transform scale ≤
            constant * distortion ^ (power + Module.finrank ℤ integerLattice + 1) := by
  obtain ⟨hull, hullCompact, supported⟩ := exists_hull finiteTest finiteSupport parameters compact
  obtain ⟨bound, bounded⟩ := finiteSupport.exists_bound_of_continuous finiteContinuous
  obtain ⟨constant, nonnegative, boundAt⟩ := BanachRationalUniformDecay.uniform_tail realTest hull hullCompact bound power
  exact ⟨constant, nonnegative, fun parameter membership transform distortion distortionNonnegative distortionBound scale scaleLower =>
    boundAt (FiniteParameterThetaDecay.pullback finiteTest parameter) (supported parameter membership)
      (fun _ => bounded _) transform distortion distortionNonnegative distortionBound scale scaleLower⟩

theorem uniform_small (realTest : SchwartzMap RealSpace Target) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameters : Set Parameter) (compact : IsCompact parameters) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter ∈ parameters,
      ∀ (transform : RealSpace ≃L[ℝ] RealSpace) (scale : ℝ), 0 < scale →
        Summable (fun matrix => ‖tailTerm realTest (FiniteParameterThetaDecay.pullback finiteTest parameter)
          transform.toContinuousLinearMap scale matrix‖) ∧
        scale ^ 7 * absoluteTail realTest finiteTest parameter transform.toContinuousLinearMap scale ≤
          constant * ‖transform.symm.toContinuousLinearMap‖ ^ 7 := by
  obtain ⟨constant, nonnegative, bounded⟩ := uniform_large realTest finiteTest finiteContinuous finiteSupport parameters compact 0
  refine ⟨constant, nonnegative, fun parameter membership transform scale positive => ?_⟩
  obtain ⟨summable, estimate⟩ := bounded parameter membership (scale • transform.toContinuousLinearMap)
    (scale⁻¹ * ‖transform.symm.toContinuousLinearMap‖) (by positivity)
    (UniformAbsoluteTheta.scaled_inverse_bound transform scale positive) 1 le_rfl
  have termEquality (matrix : Rectangular ℚ) :
      tailTerm realTest (FiniteParameterThetaDecay.pullback finiteTest parameter) (scale • transform.toContinuousLinearMap) 1 matrix =
        tailTerm realTest (FiniteParameterThetaDecay.pullback finiteTest parameter) transform.toContinuousLinearMap scale matrix := by
    simp only [tailTerm, _root_.smul_apply, one_smul]
  simp only [absoluteTail, termEquality, one_pow, one_mul, zero_add, RectangularFourierLinear.lattice_rank] at estimate
  refine ⟨by simpa only [termEquality] using summable, ?_⟩
  calc
    _ ≤ scale ^ 7 * (constant * (scale⁻¹ * ‖transform.symm.toContinuousLinearMap‖) ^ 7) :=
      mul_le_mul_of_nonneg_left estimate (pow_nonneg positive.le _)
    _ = _ := by rw [mul_pow]; field_simp

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachAbsoluteTheta
