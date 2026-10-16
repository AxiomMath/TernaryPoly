module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineRealCoefficient

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def standardGoodLineIntegralMatrix (first second : IntegralAdeles) : GeneralLinearGroup (Fin 3) IntegralAdeles :=
  ⟨!![0,1,0;1,0,0;second,first,1], !![0,1,0;1,0,0;-first,-second,1], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem standardGoodLineFiniteArgument_integral (finite : FiniteAwayThree × FiniteAwayThree)
    (first_mem : finite.1.val ∈ Set.range integralEmbedding)
    (second_mem : finite.2.val ∈ Set.range integralEmbedding) :
    standardGoodLineFiniteArgument finite ∈ Set.range (GeneralLinearGroup.map integralEmbedding) := by
  obtain ⟨first, first_eq⟩ := first_mem
  obtain ⟨second, second_eq⟩ := second_mem
  refine ⟨standardGoodLineIntegralMatrix first second, ?_⟩
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [standardGoodLineIntegralMatrix, standardGoodLineFiniteArgument, weyl, lineUnipotent, upperUnipotent,
      rationalFinite, rationalGoodLine, Matrix.mul_apply, Fin.sum_univ_three, first_eq, second_eq]

/-- On integral finite radical coordinates the actual archimedean integral has no finite scalar factor. -/
theorem goodLineMixedArchimedeanIntegral_integral_region {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree)
    (first_mem : finite.1.val ∈ Set.range integralEmbedding)
    (second_mem : finite.2.val ∈ Set.range integralEmbedding) :
    goodLineMixedArchimedeanIntegral flat parameter matrix functional finite =
      goodLineSourceKernelIntegral data.chi source parameter matrix functional finite := by
  obtain ⟨compact, compact_eq⟩ := standardGoodLineFiniteArgument_integral finite first_mem second_mem
  apply integral_congr_ae
  filter_upwards [] with real
  have values : (fun vertices => flat parameter vertices
      (combineGL (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite))) =
      standardGoodLineRealKernel parameter real •
        sourceRealTranslate data.chi source (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite) := by
    funext vertices
    change flat parameter vertices _ = standardGoodLineRealKernel parameter real • _
    rw [← compact_eq, polynomialFlatSection_value_real_integral data flat sections, endpoint,
      realPlaneFlatWeight_standardGoodLine, compact_eq,
      sourceCocycle_real_translate data .plane source cocycle]
    rfl
  rw [values, map_smul, map_smul, smul_eq_mul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
