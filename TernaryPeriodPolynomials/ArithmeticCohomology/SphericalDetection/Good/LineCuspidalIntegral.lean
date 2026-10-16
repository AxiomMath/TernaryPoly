module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.FiniteFlatSection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def standardGoodLineFiniteCuspWeight (degree : ℕ) (parameter : ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) : ℂ :=
  normPower (finiteAdeleUnit (GeneralLinearGroup.det (standardGoodLineFiniteCoordinates finite).block))
      (binaryInductionExponent degree .plane parameter) *
    normPower (finiteAdeleUnit (standardGoodLineFiniteCoordinates finite).scalar)
      (-2 * inductionExponent .plane parameter)

theorem standardGoodLineFiniteCuspWeight_ne_zero (degree : ℕ) (parameter : ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) : standardGoodLineFiniteCuspWeight degree parameter finite ≠ 0 :=
  mul_ne_zero (normPower_ne_zero _ _) (normPower_ne_zero _ _)

theorem standardGoodLineFiniteCuspWeight_analyticAt (degree : ℕ) (parameter : ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    AnalyticAt ℂ (fun parameter => standardGoodLineFiniteCuspWeight degree parameter finite) parameter := by
  unfold standardGoodLineFiniteCuspWeight normPower binaryInductionExponent inductionExponent
  fun_prop

/-- The remaining real integral evaluates the actual source cusp tensor at a finite binary matrix away from three. -/
def goodLineCuspidalArchimedeanIntegral {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) : ℂ :=
  ∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter real *
    functional (goodLineMixedRealCoordinate degree matrix (fun vertices =>
      (sourcePlaneCuspidalValues data source cocycle vertices (atInfinity (standardGoodLineRealArgument real))).val
        (atFinite (standardGoodLineFiniteCoordinates finite).block)))
    ∂((volume : Measure ℝ).prod volume)

theorem polynomialFlatSection_standardGoodLine_cuspidal {degree : ℕ} (data : InducingData degree)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (parameter : ℂ) (vertices : Fin 3 → RealGL3) (real : ℝ × ℝ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    flat parameter vertices (combineGL (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite)) =
      (standardGoodLineRealKernel parameter real * standardGoodLineFiniteCuspWeight degree parameter finite) •
        (sourcePlaneCuspidalValues data source cocycle vertices (atInfinity (standardGoodLineRealArgument real))).val
          (atFinite (standardGoodLineFiniteCoordinates finite).block) := by
  simpa only [standardGoodLineRealKernel, standardGoodLineFiniteCuspWeight, mul_assoc,
    realPlaneFlatWeight_standardGoodLine] using
    polynomialFlatSection_value_plane_level data trivial source cocycle flat sections endpoint parameter vertices
      (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite) (standardGoodLineFiniteCoordinates finite)

theorem goodLineMixedArchimedeanIntegral_cuspidal {degree : ℕ} (data : InducingData degree)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    goodLineMixedArchimedeanIntegral flat parameter matrix functional finite =
      standardGoodLineFiniteCuspWeight degree parameter finite *
        goodLineCuspidalArchimedeanIntegral data source cocycle parameter matrix functional finite := by
  rw [goodLineCuspidalArchimedeanIntegral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with real
  have values : (fun vertices => flat parameter vertices
      (combineGL (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite))) =
      (standardGoodLineRealKernel parameter real * standardGoodLineFiniteCuspWeight degree parameter finite) •
        (fun vertices => (sourcePlaneCuspidalValues data source cocycle vertices
          (atInfinity (standardGoodLineRealArgument real))).val (atFinite (standardGoodLineFiniteCoordinates finite).block)) := by
    funext vertices
    exact polynomialFlatSection_standardGoodLine_cuspidal data trivial source cocycle flat sections endpoint
      parameter vertices real finite
  rw [values, map_smul, map_smul, smul_eq_mul]
  ring

theorem goodLineMixedRealCoordinate_cuspidal_continuation {degree : ℕ}
    (local_entry : LocalBadPlaneEntry) (data : InducingData degree) (trivial : data.chi = trivialCharacter)
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
      Integrable (fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
        goodLineCuspidalArchimedeanIntegral data source cocycle parameter matrix functional finite)
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      functional (goodLineMixedRealCoordinate degree matrix (goodLineComplementFamily standard parameter)) =
        ∫ finite, standardGoodLineFiniteCuspWeight degree parameter finite *
          goodLineCuspidalArchimedeanIntegral data source cocycle parameter matrix functional finite
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
      fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
        goodLineCuspidalArchimedeanIntegral data source cocycle parameter matrix functional finite := by
    funext finite
    exact goodLineMixedArchimedeanIntegral_cuspidal data trivial source cocycle flat sections endpoint
      parameter matrix functional finite
  simpa only [equality] using formula parameter beyond

end TernaryPeriodPolynomials.SphericalDetection.Helpers
