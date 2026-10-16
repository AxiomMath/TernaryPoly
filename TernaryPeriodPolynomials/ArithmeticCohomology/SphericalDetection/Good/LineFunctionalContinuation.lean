module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PolynomialFunctionalContinuation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def standardGoodLineAwayPolynomial {degree : ℕ} (flat : ℂ → SourceCochain degree)
    (parameter : ℂ) (vertices : Fin 3 → RealGL3) (away : AdelesAwayThree × AdelesAwayThree) :
    HomogeneousPoly degree :=
  flat parameter vertices (weyl⁻¹ * lineUnipotent (adeleAwayThreeScalar away.1)
    (adeleAwayThreeScalar away.2) * rationalGroup rationalGoodLine)

/-- The complementary continuation can be tested by any polynomial linear functional. -/
theorem goodLineComplementFamily_functional_continuation {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat standard : ℂ → SourceCochain degree)
    (flat_sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint_support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (flat cohomologicalPoint vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial))
    (vertices : Fin 3 → RealGL3) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    (∀ parameter, MeromorphicAt (fun parameter =>
      functional (goodLineComplementFamily standard parameter vertices)) parameter) ∧
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (fun away => functional (standardGoodLineAwayPolynomial flat parameter vertices away)) radicalAwayThreeMeasure ∧
      functional (goodLineComplementFamily standard parameter vertices) =
        ∫ away, functional (standardGoodLineAwayPolynomial flat parameter vertices away) ∂radicalAwayThreeMeasure := by
  apply ternaryPolynomialFunctional_integral_continuation
  intro monomial
  refine ⟨(goodLineComplementFamily_continuation local_entry data flat standard flat_sections
    endpoint_support continuations vertices monomial).1, ?_⟩
  obtain ⟨threshold, formula⟩ := standardContinuation_goodLine_factor local_entry data
    (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
    (fun parameter argument => (standard parameter vertices argument).val.coeff monomial)
    (flat_sections vertices monomial) (endpoint_support vertices monomial) (continuations vertices monomial)
  refine ⟨threshold, ?_⟩
  intro parameter beyond
  obtain ⟨integrable, value⟩ := formula parameter beyond
  refine ⟨integrable, ?_⟩
  rw [goodLineComplementFamily_coeff, value]
  change (9 : ℂ) * ((1 / 9 : ℂ) *
    ∫ away, (standardGoodLineAwayPolynomial flat parameter vertices away).val.coeff monomial ∂radicalAwayThreeMeasure) = _
  ring

theorem goodLineComplementFamily_functional_archimedean_finite {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat standard : ℂ → SourceCochain degree)
    (flat_sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint_support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (flat cohomologicalPoint vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial))
    (vertices : Fin 3 → RealGL3) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (standardGoodLineArchimedeanIntegral
        (fun parameter argument => functional (flat parameter vertices argument)) parameter)
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      functional (goodLineComplementFamily standard parameter vertices) =
        ∫ finite, standardGoodLineArchimedeanIntegral
          (fun parameter argument => functional (flat parameter vertices argument)) parameter finite
          ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  obtain ⟨_, threshold, formula⟩ := goodLineComplementFamily_functional_continuation local_entry data flat standard
    flat_sections endpoint_support continuations vertices functional
  refine ⟨threshold, ?_⟩
  intro parameter beyond
  obtain ⟨integrable, value⟩ := formula parameter beyond
  obtain ⟨iterated_integrable, iterated_value⟩ := standardGoodLineAwayIntegral_fubini
    (fun parameter argument => functional (flat parameter vertices argument)) parameter integrable
  exact ⟨iterated_integrable, value.trans iterated_value⟩

theorem goodLineComplementFamily_functional_analytic {degree : ℕ} (standard : ℂ → SourceCochain degree)
    (analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (standard parameter vertices argument).val.coeff monomial) cohomologicalPoint)
    (vertices : Fin 3 → RealGL3) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    AnalyticAt ℂ (fun parameter => functional (goodLineComplementFamily standard parameter vertices)) cohomologicalPoint :=
  ternaryPolynomialFunctional_analyticAt _ cohomologicalPoint
    (goodLineComplementFamily_analytic standard analytic vertices) functional

end TernaryPeriodPolynomials.SphericalDetection.Helpers
