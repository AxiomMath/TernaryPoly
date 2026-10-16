module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ComplexClipping
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.EisensteinQuotient

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

theorem normalizedBoundaryResidue_continuous_approximation
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      (∀ matrix, ‖normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix)‖ ≤ bound) ∧
      ∃ approximation : ℕ → RealSL3 → ℂ,
        (∀ n, Continuous (approximation n)) ∧
        (∀ n matrix, ‖approximation n matrix‖ ≤ 2 * bound) ∧
        (∀ n (principal : principalRealSpecialLinear) matrix,
          approximation n (principal.val * matrix) = approximation n matrix) ∧
        (∀ matrix, Tendsto (fun n => approximation n matrix) atTop
          (nhds (normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix)))) := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedBoundaryResidue_global_bound flat continuation_spec
  let displacement (n : ℕ) : ℝ := 1 / (n + 1)
  have positive (n : ℕ) : 0 < displacement n := by dsimp [displacement]; positivity
  have limit : Tendsto displacement atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall positive⟩
  let approximation (n : ℕ) (matrix : RealSL3) := complexClip bound
    ((displacement n : ℂ) * normalizedScalarEisensteinSum degree family
      ((3 : ℂ) / 2 + (displacement n : ℂ)) (realSpecialIntegralSlice integral matrix))
  refine ⟨bound, nonnegative, fun matrix => bounded _, approximation, ?_, ?_, ?_, ?_⟩
  · intro n
    apply (complexClip_continuous bound).comp
    apply continuous_const.mul
    apply normalized_scalar_sum_continuous flat _ _ (realSpecialIntegralSlice_continuous integral)
    simpa using positive n
  · intro n matrix
    exact complexClip_norm_le nonnegative _
  · intro n principal matrix
    dsimp only [approximation]
    rw [normalizedScalarEisensteinSum_principal_slice_invariant flat]
  · intro matrix
    have converges := (complexClip_continuous bound).continuousAt.tendsto.comp
      ((normalizedBoundaryResidue_tendsto flat continuation_spec (realSpecialIntegralSlice integral matrix)).comp limit)
    simpa only [complexClip_eq_self (bounded _), Function.comp_def, approximation,
      normalizedScalarEisensteinSum] using converges

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
