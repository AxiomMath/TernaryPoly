module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rational.UniformDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteParameterThetaDecay

abbrev Parameter := GeneralLinearGroup (Fin 3) FiniteAdeles × GeneralLinearGroup (Fin 2) FiniteAdeles

def pullback (function : Rectangular FiniteAdeles → ℂ) (parameter : Parameter) : Rectangular FiniteAdeles → ℂ :=
  fun value => function (matrixHomeomorph parameter.1 parameter.2 value)

theorem inverse_continuous : Continuous (fun pair : Parameter × Rectangular FiniteAdeles =>
    (matrixHomeomorph pair.1.1 pair.1.2).symm pair.2) := by
  change Continuous (fun pair : Parameter × Rectangular FiniteAdeles =>
    pair.1.1.val * pair.2 * pair.1.2⁻¹.val)
  exact ((Units.continuous_val.comp (continuous_fst.comp continuous_fst)).matrix_mul continuous_snd).matrix_mul
    (Units.continuous_val.comp (continuous_snd.comp continuous_fst).inv)

theorem exists_hull (finiteTest : Rectangular FiniteAdeles → ℂ) (compactSupport : HasCompactSupport finiteTest)
    (parameters : Set Parameter) (compact : IsCompact parameters) :
    ∃ hull : Set (Rectangular FiniteAdeles), IsCompact hull ∧ ∀ parameter ∈ parameters,
      ∀ value, value ∉ hull → pullback finiteTest parameter value = 0 := by
  let hull := (fun pair : Parameter × Rectangular FiniteAdeles => (matrixHomeomorph pair.1.1 pair.1.2).symm pair.2) ''
    (parameters ×ˢ tsupport finiteTest)
  refine ⟨hull, (compact.prod compactSupport).image inverse_continuous, ?_⟩
  intro parameter membership value outside
  by_contra nonzero
  apply outside
  exact ⟨(parameter, matrixHomeomorph parameter.1 parameter.2 value), ⟨membership, subset_closure nonzero⟩,
    (matrixHomeomorph parameter.1 parameter.2).symm_apply_apply value⟩

theorem uniform_large (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameters : Set Parameter) (compact : IsCompact parameters) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter ∈ parameters,
      ∀ (transform : RealSpace →L[ℝ] RealSpace) (distortion : ℝ), 0 ≤ distortion →
        (∀ vector, ‖vector‖ ≤ distortion * ‖transform vector‖) → ∀ scale : ℝ, 1 ≤ scale →
          scale ^ power * ‖(∑' matrix : Rectangular ℚ, realTest (scale • transform (realVector matrix)) *
            pullback finiteTest parameter (finiteMatrix matrix)) - realTest 0 * finiteTest 0‖ ≤
              constant * distortion ^ (power + Module.finrank ℤ integerLattice + 1) := by
  obtain ⟨hull, hullCompact, supportBound⟩ := exists_hull finiteTest finiteSupport parameters compact
  obtain ⟨bound, boundProperty⟩ := finiteSupport.exists_bound_of_continuous finiteContinuous
  obtain ⟨constant, nonnegative, bounded⟩ := RationalUniformDecay.uniform_remainder realTest hull hullCompact bound power
  refine ⟨constant, nonnegative, fun parameter membership transform distortion distortionNonnegative distortionBound scale scaleLower => ?_⟩
  have zeroValue : pullback finiteTest parameter 0 = finiteTest 0 := by
    change finiteTest (RectangularTransport.matrixEquiv parameter.1 parameter.2 0) = finiteTest 0
    rw [map_zero]
  simpa only [zeroValue] using bounded (pullback finiteTest parameter) (supportBound parameter membership)
    (fun value => boundProperty _) transform distortion distortionNonnegative distortionBound scale scaleLower

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteParameterThetaDecay
