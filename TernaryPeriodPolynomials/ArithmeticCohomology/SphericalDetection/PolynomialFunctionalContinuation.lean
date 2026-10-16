module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Continuation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem scalarIntegralContinuation_add {Ω : Type*} [MeasurableSpace Ω] (measure : Measure Ω)
    (first_flat second_flat : ℂ → Ω → ℂ) (first second : ℂ → ℂ)
    (first_result : (∀ parameter, MeromorphicAt first parameter) ∧
      ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
        Integrable (first_flat parameter) measure ∧ first parameter = ∫ point, first_flat parameter point ∂measure)
    (second_result : (∀ parameter, MeromorphicAt second parameter) ∧
      ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
        Integrable (second_flat parameter) measure ∧ second parameter = ∫ point, second_flat parameter point ∂measure) :
    (∀ parameter, MeromorphicAt (first + second) parameter) ∧
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (fun point => first_flat parameter point + second_flat parameter point) measure ∧
      (first + second) parameter = ∫ point, first_flat parameter point + second_flat parameter point ∂measure := by
  obtain ⟨first_meromorphic, first_bound, first_integral⟩ := first_result
  obtain ⟨second_meromorphic, second_bound, second_integral⟩ := second_result
  refine ⟨fun parameter => (first_meromorphic parameter).add (second_meromorphic parameter),
    max first_bound second_bound, ?_⟩
  intro parameter beyond
  obtain ⟨first_integrable, first_value⟩ := first_integral parameter (lt_of_le_of_lt (le_max_left _ _) beyond)
  obtain ⟨second_integrable, second_value⟩ := second_integral parameter (lt_of_le_of_lt (le_max_right _ _) beyond)
  refine ⟨first_integrable.add second_integrable, ?_⟩
  change first parameter + second parameter = _
  rw [integral_add first_integrable second_integrable, first_value, second_value]

theorem scalarIntegralContinuation_sub {Ω : Type*} [MeasurableSpace Ω] (measure : Measure Ω)
    (first_flat second_flat : ℂ → Ω → ℂ) (first second : ℂ → ℂ)
    (first_result : (∀ parameter, MeromorphicAt first parameter) ∧
      ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
        Integrable (first_flat parameter) measure ∧ first parameter = ∫ point, first_flat parameter point ∂measure)
    (second_result : (∀ parameter, MeromorphicAt second parameter) ∧
      ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
        Integrable (second_flat parameter) measure ∧ second parameter = ∫ point, second_flat parameter point ∂measure) :
    (∀ parameter, MeromorphicAt (first - second) parameter) ∧
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (fun point => first_flat parameter point - second_flat parameter point) measure ∧
      (first - second) parameter = ∫ point, first_flat parameter point - second_flat parameter point ∂measure := by
  obtain ⟨first_meromorphic, first_bound, first_integral⟩ := first_result
  obtain ⟨second_meromorphic, second_bound, second_integral⟩ := second_result
  refine ⟨fun parameter => (first_meromorphic parameter).sub (second_meromorphic parameter),
    max first_bound second_bound, ?_⟩
  intro parameter beyond
  obtain ⟨first_integrable, first_value⟩ := first_integral parameter (lt_of_le_of_lt (le_max_left _ _) beyond)
  obtain ⟨second_integrable, second_value⟩ := second_integral parameter (lt_of_le_of_lt (le_max_right _ _) beyond)
  refine ⟨first_integrable.sub second_integrable, ?_⟩
  change first parameter - second parameter = _
  rw [integral_sub first_integrable second_integrable, first_value, second_value]

/-- Coefficientwise continuation of a homogeneous polynomial family extends to every linear functional. -/
theorem ternaryPolynomialFunctional_integral_continuation {degree : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (measure : Measure Ω) (flat : ℂ → Ω → HomogeneousPoly degree) (family : ℂ → HomogeneousPoly degree)
    (coefficients : ∀ monomial : Fin 3 →₀ ℕ,
      (∀ parameter, MeromorphicAt (fun parameter => (family parameter).val.coeff monomial) parameter) ∧
      ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
        Integrable (fun point => (flat parameter point).val.coeff monomial) measure ∧
        (family parameter).val.coeff monomial =
          ∫ point, (flat parameter point).val.coeff monomial ∂measure)
    (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    (∀ parameter, MeromorphicAt (fun parameter => functional (family parameter)) parameter) ∧
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (fun point => functional (flat parameter point)) measure ∧
      functional (family parameter) = ∫ point, functional (flat parameter point) ∂measure := by
  have spanned := ternaryPolynomialDual_mem_span_coefficients functional
  induction spanned using Submodule.span_induction with
  | mem functional member =>
    obtain ⟨monomial, rfl⟩ := member
    exact coefficients monomial
  | zero =>
    refine ⟨fun _ => analyticAt_const.meromorphicAt, 0, ?_⟩
    intro parameter _
    exact ⟨integrable_zero _ _ _, (integral_zero _ _).symm⟩
  | add first second _ _ first_result second_result =>
    obtain ⟨first_meromorphic, first_bound, first_integral⟩ := first_result
    obtain ⟨second_meromorphic, second_bound, second_integral⟩ := second_result
    refine ⟨fun parameter => (first_meromorphic parameter).add (second_meromorphic parameter),
      max first_bound second_bound, ?_⟩
    intro parameter beyond
    obtain ⟨first_integrable, first_value⟩ := first_integral parameter (lt_of_le_of_lt (le_max_left _ _) beyond)
    obtain ⟨second_integrable, second_value⟩ := second_integral parameter (lt_of_le_of_lt (le_max_right _ _) beyond)
    refine ⟨first_integrable.add second_integrable, ?_⟩
    change first (family parameter) + second (family parameter) =
      ∫ point, first (flat parameter point) + second (flat parameter point) ∂measure
    rw [integral_add first_integrable second_integrable, first_value, second_value]
  | smul scalar functional _ result =>
    obtain ⟨meromorphic, threshold, integral⟩ := result
    refine ⟨fun parameter => (meromorphic parameter).const_smul scalar, threshold, ?_⟩
    intro parameter beyond
    obtain ⟨integrable, value⟩ := integral parameter beyond
    refine ⟨integrable.const_mul scalar, ?_⟩
    change scalar * functional (family parameter) = ∫ point, scalar * functional (flat parameter point) ∂measure
    rw [integral_const_mul, value]

theorem ternaryPolynomialFunctional_analyticAt {degree : ℕ}
    (family : ℂ → HomogeneousPoly degree) (endpoint : ℂ)
    (coefficients : ∀ monomial : Fin 3 →₀ ℕ,
      AnalyticAt ℂ (fun parameter => (family parameter).val.coeff monomial) endpoint)
    (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    AnalyticAt ℂ (fun parameter => functional (family parameter)) endpoint := by
  have spanned := ternaryPolynomialDual_mem_span_coefficients functional
  induction spanned using Submodule.span_induction with
  | mem functional member =>
    obtain ⟨monomial, rfl⟩ := member
    exact coefficients monomial
  | zero => exact analyticAt_const
  | add first second _ _ first_result second_result => exact first_result.add second_result
  | smul scalar functional _ result => exact result.const_smul

end TernaryPeriodPolynomials.SphericalDetection.Helpers
