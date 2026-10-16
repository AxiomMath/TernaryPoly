module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.FlatSectionWeight
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineMixedArchimedeanIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineMixedRealCoordinate_flat_weight {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (parameter : ℂ) (matrix : Matrix.GeneralLinearGroup (Fin 2) ℤ) (argument : AdelicGL) :
    goodLineMixedRealCoordinate degree matrix (fun vertices => flat parameter vertices argument) =
      planeFlatWeight parameter argument •
        goodLineMixedRealCoordinate degree matrix (fun vertices => source vertices argument) := by
  have values : (fun vertices => flat parameter vertices argument) =
      planeFlatWeight parameter argument • (fun vertices => source vertices argument) := by
    funext vertices
    simpa only [endpoint, Pi.smul_apply] using
      polynomialFlatSection_value_weight data flat sections parameter vertices argument
  rw [values, map_smul]

/-- The archimedean integral expressed using the supplied source itself. -/
def goodLineWeightedSourceIntegral {degree : ℕ} (source : SourceCochain degree) (parameter : ℂ)
    (matrix : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) : ℂ :=
  ∫ real : ℝ × ℝ,
    planeFlatWeight parameter (combineGL (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite)) *
      functional (goodLineMixedRealCoordinate degree matrix (fun vertices => source vertices
        (combineGL (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite))))
    ∂((volume : Measure ℝ).prod volume)

theorem goodLineMixedArchimedeanIntegral_eq_weighted_source {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (parameter : ℂ) (matrix : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    goodLineMixedArchimedeanIntegral flat parameter matrix functional finite =
      goodLineWeightedSourceIntegral source parameter matrix functional finite := by
  apply integral_congr_ae
  filter_upwards [] with real
  rw [goodLineMixedRealCoordinate_flat_weight data source flat sections endpoint, map_smul, smul_eq_mul]

theorem goodLineMixedRealCoordinate_weighted_source_continuation {degree : ℕ}
    (local_entry : LocalBadPlaneEntry) (data : InducingData degree)
    (source : SourceCochain degree) (flat standard : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (source vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial))
    (matrix : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (goodLineWeightedSourceIntegral source parameter matrix functional)
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      functional (goodLineMixedRealCoordinate degree matrix (goodLineComplementFamily standard parameter)) =
        ∫ finite, goodLineWeightedSourceIntegral source parameter matrix functional finite
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
      goodLineWeightedSourceIntegral source parameter matrix functional := by
    funext finite
    exact goodLineMixedArchimedeanIntegral_eq_weighted_source data source flat sections endpoint
      parameter matrix functional finite
  simpa only [equality] using formula parameter beyond

end TernaryPeriodPolynomials.SphericalDetection.Helpers
