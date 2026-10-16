module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineMixedContinuation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineMixedArchimedeanIntegral {degree : ℕ} (flat : ℂ → SourceCochain degree) (parameter : ℂ)
    (matrix : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) : ℂ :=
  ∫ real : ℝ × ℝ, functional (goodLineMixedRealCoordinate degree matrix
    (fun vertices => flat parameter vertices
      (combineGL (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite))))
    ∂((volume : Measure ℝ).prod volume)

theorem goodLineMixedAwayIntegral_fubini {degree : ℕ} (flat : ℂ → SourceCochain degree) (parameter : ℂ)
    (matrix : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (integrable : Integrable (fun away => functional (goodLineMixedRealCoordinate degree matrix
      (fun vertices => standardGoodLineAwayPolynomial flat parameter vertices away))) radicalAwayThreeMeasure) :
    Integrable (goodLineMixedArchimedeanIntegral flat parameter matrix functional)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
    (∫ away, functional (goodLineMixedRealCoordinate degree matrix
      (fun vertices => standardGoodLineAwayPolynomial flat parameter vertices away)) ∂radicalAwayThreeMeasure) =
      ∫ finite, goodLineMixedArchimedeanIntegral flat parameter matrix functional finite
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  have lifted := awayRadicalJoin_measurePreserving.integrable_comp_of_integrable integrable
  have inner : (fun finite => ∫ real : ℝ × ℝ,
      functional (goodLineMixedRealCoordinate degree matrix
        (fun vertices => standardGoodLineAwayPolynomial flat parameter vertices (awayRadicalJoin (real, finite))))
      ∂((volume : Measure ℝ).prod volume)) = goodLineMixedArchimedeanIntegral flat parameter matrix functional := by
    funext finite
    apply integral_congr_ae
    filter_upwards [] with real
    apply congrArg functional
    apply congrArg (goodLineMixedRealCoordinate degree matrix)
    funext vertices
    exact congrArg (flat parameter vertices) (standardGoodLineArgument_combine real finite)
  constructor
  · rw [← inner]
    exact lifted.integral_prod_right
  · rw [← awayRadicalJoin_measurePreserving.integral_comp awayRadicalJoin.measurableEmbedding]
    have split := integral_prod_symm _ lifted
    dsimp only [Function.comp_def] at split
    rw [split, inner]

/-- The actual mixed binary projection continues the iterated complementary integral. -/
theorem goodLineMixedRealCoordinate_archimedean_finite {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat standard : ℂ → SourceCochain degree)
    (flat_sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint_support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (flat cohomologicalPoint vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial))
    (matrix : Matrix.GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (goodLineMixedArchimedeanIntegral flat parameter matrix functional)
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      functional (goodLineMixedRealCoordinate degree matrix (goodLineComplementFamily standard parameter)) =
        ∫ finite, goodLineMixedArchimedeanIntegral flat parameter matrix functional finite
          ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  obtain ⟨_, threshold, formula⟩ := goodLineMixedRealCoordinate_continuation local_entry data flat standard
    flat_sections endpoint_support continuations matrix functional
  refine ⟨threshold, ?_⟩
  intro parameter beyond
  obtain ⟨integrable, value⟩ := formula parameter beyond
  obtain ⟨iterated_integrable, iterated_value⟩ := goodLineMixedAwayIntegral_fubini flat parameter matrix functional integrable
  exact ⟨iterated_integrable, value.trans iterated_value⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
