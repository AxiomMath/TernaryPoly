module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineVertexProjection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def sourceRealPrismDifferential {degree : ℕ} (character : RankOneCharacter)
    (source : SourceCochain degree) (real : RealGL3) (finite : FiniteGL)
    (vertices : Fin 3 → RealGL3) : HomogeneousPoly degree :=
  sourceRealVertexPrism character source realUpperLeftLeviProjection real finite ![vertices 1, vertices 2] -
    sourceRealVertexPrism character source realUpperLeftLeviProjection real finite ![vertices 0, vertices 2] +
    sourceRealVertexPrism character source realUpperLeftLeviProjection real finite ![vertices 0, vertices 1]

theorem goodLineMixedRealCoordinate_source_prism {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (real : ℝ × ℝ) (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedRealCoordinate degree matrix
      (sourceRealTranslate data.chi source (standardGoodLineRealArgument real) finite) =
    goodLineMixedRealCoordinate degree matrix
      (sourceRealPrismDifferential data.chi source (standardGoodLineRealArgument real) finite) := by
  have identity : sourceRealTranslate data.chi source (standardGoodLineRealArgument real) finite -
      sourceProjectedRealTranslate data.chi source realUpperLeftLeviProjection (standardGoodLineRealArgument real) finite =
        sourceRealPrismDifferential data.chi source (standardGoodLineRealArgument real) finite := by
    funext vertices
    exact sourceRealTranslate_prism data .plane source cocycle realUpperLeftLeviProjection
      (standardGoodLineRealArgument real) finite vertices
  have mixed := congrArg (goodLineMixedRealCoordinate degree matrix) identity
  rw [map_sub, goodLineMixedRealCoordinate_projected_zero data source cocycle diagonal, sub_zero] at mixed
  exact mixed

/-- Equality of the full integrands, before any integration of the individual prism terms. -/
theorem goodLineSourceKernelIntegral_prism {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    goodLineSourceKernelIntegral data.chi source parameter matrix functional finite =
      ∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter real *
        functional (goodLineMixedRealCoordinate degree matrix
          (sourceRealPrismDifferential data.chi source (standardGoodLineRealArgument real)
            (standardGoodLineFiniteArgument finite))) ∂((volume : Measure ℝ).prod volume) := by
  apply integral_congr_ae
  filter_upwards [] with real
  rw [goodLineMixedRealCoordinate_source_prism data source cocycle diagonal]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
