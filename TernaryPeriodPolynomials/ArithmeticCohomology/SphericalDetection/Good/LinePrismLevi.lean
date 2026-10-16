module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineRealLeviMeasure
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PrismCovariance

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realUpperLeftLeviProjection_planeLevi_standardGoodLine (block : BinaryRealGL) (real : ℝ × ℝ) :
    realUpperLeftLeviProjection (planeLevi block 1 * standardGoodLineRealArgument real) =
      planeLevi block 1 * realUpperLeftLeviProjection (standardGoodLineRealArgument real) := by
  have upper : upperLeftBlock (planeLevi block 1 * standardGoodLineRealArgument real).val =
      (block * binaryPivotSwap).val := by
    change upperLeftBlock ((planeLevi block 1).val * (standardGoodLineRealArgument real).val) = _
    rw [standardGoodLineRealArgument_val]
    funext row column
    fin_cases row <;> fin_cases column <;>
      simp [upperLeftBlock, planeLevi, planeBlock, binaryPivotSwap, Matrix.mul_apply, Fin.sum_univ_three,
        Fin.sum_univ_two]
  rw [realUpperLeftLeviProjection_standardGoodLine, realUpperLeftLeviProjection, upper, invertibleMatrix_coe]
  exact planeLeviOneHom.map_mul block binaryPivotSwap

theorem sourceRealVertexPrism_goodLine_radical_levi {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (block : BinaryRealGL) (real : ℝ × ℝ) (finite : FiniteGL) (radical : RadicalLattice) :
    sourceRealVertexPrism data.chi source realUpperLeftLeviProjection
      (planeLevi block 1 * standardGoodLineRealArgument real) finite
      ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)] =
    sourceRealVertexPrism data.chi
      (fun vertices argument => source vertices (argument * atInfinity (planeLevi block 1)))
      realUpperLeftLeviProjection (standardGoodLineRealArgument real) finite
      ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)] := by
  apply sourceRealVertexPrism_left_translate data .plane source cocycle realUpperLeftLeviProjection
    (planeLevi block 1) (standardGoodLineRealArgument real)
    ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)] finite
  intro index
  fin_cases index
  · change realUpperLeftLeviProjection (planeLevi block 1 * (standardGoodLineRealArgument real * 1)) =
      planeLevi block 1 * realUpperLeftLeviProjection (standardGoodLineRealArgument real * 1)
    simp only [mul_one]
    exact realUpperLeftLeviProjection_planeLevi_standardGoodLine block real
  · change realUpperLeftLeviProjection (planeLevi block 1 *
        (standardGoodLineRealArgument real * GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical))) =
      planeLevi block 1 * realUpperLeftLeviProjection
        (standardGoodLineRealArgument real * GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical))
    rw [standardGoodLineRealArgument_radical]
    exact realUpperLeftLeviProjection_planeLevi_standardGoodLine block _

/-- The left Levi change acts on the original source's adelic argument. -/
theorem sourceRealVertexPrism_goodLine_levi_change {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (real : ℝ × ℝ) (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    sourceRealVertexPrism data.chi source realUpperLeftLeviProjection
      (standardGoodLineRealArgument real * GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix))
      finite ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)] =
    sourceRealVertexPrism data.chi
      (fun vertices argument => source vertices (argument * atInfinity (goodLineConjugateRealLevi matrix)))
      realUpperLeftLeviProjection (standardGoodLineRealArgument (goodLineLeviRealInput matrix real))
      finite ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)] := by
  rw [standardGoodLineRealArgument_levi]
  exact sourceRealVertexPrism_goodLine_radical_levi data source cocycle _ _ finite radical

theorem integral_goodLinePrism_radical_levi_change {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice)
    (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) (parameter : ℂ) :
    (∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter real *
      functional (sourceRealVertexPrism data.chi source realUpperLeftLeviProjection
        (standardGoodLineRealArgument real * GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix))
        finite ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)])
      ∂((volume : Measure ℝ).prod volume)) =
    ∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter (goodLineLeviRealInput matrix⁻¹ real) *
      functional (sourceRealVertexPrism data.chi
        (fun vertices argument => source vertices (argument * atInfinity (goodLineConjugateRealLevi matrix)))
        realUpperLeftLeviProjection (standardGoodLineRealArgument real)
        finite ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)])
      ∂((volume : Measure ℝ).prod volume) := by
  simp_rw [sourceRealVertexPrism_goodLine_levi_change data source cocycle]
  have translated := integral_goodLineLeviRealInput
    (fun real => standardGoodLineRealKernel parameter (goodLineLeviRealInput matrix⁻¹ real) *
      functional (sourceRealVertexPrism data.chi
        (fun vertices argument => source vertices (argument * atInfinity (goodLineConjugateRealLevi matrix)))
        realUpperLeftLeviProjection (standardGoodLineRealArgument real)
        finite ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)])) matrix
  simpa only [goodLineLeviRealInput_mul, mul_inv_cancel, goodLineLeviRealInput_one] using translated

end TernaryPeriodPolynomials.SphericalDetection.Helpers
