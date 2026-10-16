module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.FlatSectionRealFinite
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.RealTranslation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def standardGoodLineRealKernel (parameter : ℂ) (real : ℝ × ℝ) : ℂ :=
  Complex.exp ((-(3 : ℂ) / 4 - parameter / 2) * (Real.log (1 + real.1 ^ 2 + real.2 ^ 2) : ℂ))

theorem standardGoodLineRealKernel_ne_zero (parameter : ℂ) (real : ℝ × ℝ) :
    standardGoodLineRealKernel parameter real ≠ 0 := Complex.exp_ne_zero _

theorem standardGoodLineRealKernel_endpoint (real : ℝ × ℝ) :
    standardGoodLineRealKernel cohomologicalPoint real = 1 := by
  rw [standardGoodLineRealKernel, ← realPlaneFlatWeight_standardGoodLine, realPlaneFlatWeight_endpoint]

theorem standardGoodLineRealKernel_analyticAt (parameter : ℂ) (real : ℝ × ℝ) :
    AnalyticAt ℂ (fun parameter => standardGoodLineRealKernel parameter real) parameter := by
  unfold standardGoodLineRealKernel
  fun_prop

theorem standardGoodLineRealKernel_continuous (parameter : ℂ) :
    Continuous (standardGoodLineRealKernel parameter) := by
  have positive (real : ℝ × ℝ) : 0 < 1 + real.1 ^ 2 + real.2 ^ 2 := by positivity
  have base : Continuous (fun real : ℝ × ℝ => 1 + real.1 ^ 2 + real.2 ^ 2) := by fun_prop
  have logarithm := base.log (fun real => ne_of_gt (positive real))
  unfold standardGoodLineRealKernel
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp logarithm))

/-- The real integral retains the full coefficient twist and the translated source vertices. -/
def goodLineSourceKernelIntegral {degree : ℕ} (character : RankOneCharacter)
    (source : SourceCochain degree) (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) : ℂ :=
  ∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter real *
    functional (goodLineMixedRealCoordinate degree matrix
      (sourceRealTranslate character source (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite)))
    ∂((volume : Measure ℝ).prod volume)

theorem goodLineMixedRealCoordinate_real_finite_weight {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ) (real : RealGL3) (finite : FiniteGL) :
    goodLineMixedRealCoordinate degree matrix (fun vertices => flat parameter vertices (combineGL real finite)) =
      (realPlaneFlatWeight parameter real * finitePlaneFlatWeight parameter finite) •
        goodLineMixedRealCoordinate degree matrix (fun vertices => source vertices (combineGL real finite)) := by
  have values : (fun vertices => flat parameter vertices (combineGL real finite)) =
      (realPlaneFlatWeight parameter real * finitePlaneFlatWeight parameter finite) •
        (fun vertices => source vertices (combineGL real finite)) := by
    funext vertices
    simpa only [endpoint, Pi.smul_apply] using
      polynomialFlatSection_value_real_finite data flat sections parameter vertices real finite
  rw [values, map_smul]

theorem goodLineMixedArchimedeanIntegral_source_kernel {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    goodLineMixedArchimedeanIntegral flat parameter matrix functional finite =
      finitePlaneFlatWeight parameter (standardGoodLineFiniteArgument finite) *
        goodLineSourceKernelIntegral data.chi source parameter matrix functional finite := by
  rw [goodLineSourceKernelIntegral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with real
  rw [goodLineMixedRealCoordinate_real_finite_weight data source flat sections endpoint, map_smul, smul_eq_mul,
    realPlaneFlatWeight_standardGoodLine]
  have values : (fun vertices => source vertices
      (combineGL (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite))) =
      sourceRealTranslate data.chi source (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite) := by
    funext vertices
    exact sourceCocycle_real_translate data .plane source cocycle vertices _ _
  rw [values]
  unfold standardGoodLineRealKernel
  ring

/-- The exact standard continuation, with its real scalar kernel made explicit. -/
theorem goodLineMixedRealCoordinate_source_kernel_continuation {degree : ℕ}
    (local_entry : LocalBadPlaneEntry) (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (flat standard : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (source vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial))
    (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (fun finite => finitePlaneFlatWeight parameter (standardGoodLineFiniteArgument finite) *
        goodLineSourceKernelIntegral data.chi source parameter matrix functional finite)
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      functional (goodLineMixedRealCoordinate degree matrix (goodLineComplementFamily standard parameter)) =
        ∫ finite, finitePlaneFlatWeight parameter (standardGoodLineFiniteArgument finite) *
          goodLineSourceKernelIntegral data.chi source parameter matrix functional finite
          ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  have endpoint_support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (flat cohomologicalPoint vertices argument).val.coeff monomial) := by
    rw [endpoint]
    exact support
  obtain ⟨threshold, formula⟩ := goodLineMixedRealCoordinate_archimedean_finite local_entry data flat standard
    sections endpoint_support continuations matrix functional
  refine ⟨threshold, ?_⟩
  intro parameter beyond
  have equality : goodLineMixedArchimedeanIntegral flat parameter matrix functional =
      fun finite => finitePlaneFlatWeight parameter (standardGoodLineFiniteArgument finite) *
        goodLineSourceKernelIntegral data.chi source parameter matrix functional finite := by
    funext finite
    exact goodLineMixedArchimedeanIntegral_source_kernel data source cocycle flat sections endpoint
      parameter matrix functional finite
  simpa only [equality] using formula parameter beyond

end TernaryPeriodPolynomials.SphericalDetection.Helpers
