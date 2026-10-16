module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineWeightedSource

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem atFinite_mul_atInfinity (real : RealGL3) (finite : FiniteGL) :
    atFinite finite * atInfinity real = combineGL real finite := by
  apply adelicGL_ext
  · rw [map_mul, realGroup_atFinite, realGroup_atInfinity, one_mul, realGroup_combineGL]
  · rw [map_mul, finiteGroup_atFinite, finiteGroup_atInfinity, mul_one, finiteGroup_combineGL]

theorem sourceCocycle_real_translate {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data side source)
    (vertices : Fin 3 → RealGL3) (real : RealGL3) (finite : FiniteGL) :
    source vertices (combineGL real finite) =
      realCoefficientComponent degree data.chi real⁻¹
        (source (fun index => real * vertices index) (atFinite finite)) := by
  rw [cocycle.2.2.1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, atFinite_mul_atInfinity]

/-- The real argument acts both on the source vertices and on the full twisted coefficients. -/
def sourceRealTranslate {degree : ℕ} (character : RankOneCharacter)
    (source : SourceCochain degree) (real : RealGL3) (finite : FiniteGL) :
    (Fin 3 → RealGL3) → HomogeneousPoly degree :=
  fun vertices => realCoefficientComponent degree character real⁻¹
    (source (fun index => real * vertices index) (atFinite finite))

theorem goodLineWeightedSourceIntegral_real_translate {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    goodLineWeightedSourceIntegral source parameter matrix functional finite =
      ∫ real : ℝ × ℝ,
        planeFlatWeight parameter (combineGL (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite)) *
          functional (goodLineMixedRealCoordinate degree matrix
            (sourceRealTranslate data.chi source (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite)))
        ∂((volume : Measure ℝ).prod volume) := by
  apply integral_congr_ae
  filter_upwards [] with real
  apply congrArg (planeFlatWeight parameter
    (combineGL (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite)) * ·)
  apply congrArg functional
  apply congrArg (goodLineMixedRealCoordinate degree matrix)
  funext vertices
  exact sourceCocycle_real_translate data .plane source cocycle vertices _ _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
