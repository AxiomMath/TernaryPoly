module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.HomogeneousNormalization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineRealCoefficient

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Total Levi projection, used only where its upper-left block is invertible. -/
def realUpperLeftLeviProjection (matrix : RealGL3) : RealGL3 :=
  planeLevi (invertibleMatrix (upperLeftBlock matrix.val)) 1

theorem realUpperLeftLeviProjection_goodLine_congr (real : RealGL3)
    (zero0 : real.val 0 2 = 0) (zero1 : real.val 1 2 = 0)
    (first second : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
    (same : goodLineLeviProjection first = goodLineLeviProjection second) :
    realUpperLeftLeviProjection (real * GeneralLinearGroup.map (algebraMap ℚ ℝ) first.val) =
      realUpperLeftLeviProjection (real * GeneralLinearGroup.map (algebraMap ℚ ℝ) second.val) := by
  apply congrArg (fun block => planeLevi (invertibleMatrix block) 1)
  change upperLeftBlock (real.val * first.val.val.map (algebraMap ℚ ℝ)) =
    upperLeftBlock (real.val * second.val.val.map (algebraMap ℚ ℝ))
  rw [upperLeftBlock_mul_lower _ _ zero0 zero1, upperLeftBlock_mul_lower _ _ zero0 zero1]
  have rational_equal : upperLeftBlock first.val.val = upperLeftBlock second.val.val :=
    (goodLineLeviProjection_spec first).symm.trans
      ((congrArg integralBinaryMatrix same).trans (goodLineLeviProjection_spec second))
  apply congrArg (upperLeftBlock real.val * ·)
  funext row column
  exact congrArg (algebraMap ℚ ℝ) (congrFun (congrFun rational_equal row) column)

theorem sourceProjectedGoodLine_levi_radical_zero {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (real : RealGL3) (zero0 : real.val 0 2 = 0) (zero1 : real.val 1 2 = 0)
    (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    sourceProjectedRealTranslate data.chi source realUpperLeftLeviProjection real finite
      (goodLineRealVertices (goodLineLeviSection matrix, goodLineRadicalInclusion radical)) = 0 := by
  let vertices : Fin 3 → RealGL3 := fun index => realUpperLeftLeviProjection
    (real * goodLineRealVertices (goodLineLeviSection matrix, goodLineRadicalInclusion radical) index)
  have repeated : vertices 2 = vertices 1 := by
    apply realUpperLeftLeviProjection_goodLine_congr real zero0 zero1
      (goodLineLeviSection matrix * goodLineRadicalInclusion radical) (goodLineLeviSection matrix)
    rw [map_mul, goodLineLeviProjection_radical, mul_one]
  have tuple : vertices = ![vertices 0, vertices 1, vertices 1] := by
    funext index
    fin_cases index <;> first | rfl | exact repeated
  change realCoefficientComponent degree data.chi real⁻¹ (source vertices (atFinite finite)) = 0
  rw [tuple, sourceCocycle_repeated_last data .plane source cocycle diagonal, map_zero]

theorem sourceProjectedGoodLine_radical_levi_zero {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (real : RealGL3) (zero0 : real.val 0 2 = 0) (zero1 : real.val 1 2 = 0)
    (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    sourceProjectedRealTranslate data.chi source realUpperLeftLeviProjection real finite
      (goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix)) = 0 := by
  let vertices : Fin 3 → RealGL3 := fun index => realUpperLeftLeviProjection
    (real * goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix) index)
  have repeated : vertices 1 = vertices 0 := by
    apply realUpperLeftLeviProjection_goodLine_congr real zero0 zero1
      (goodLineRadicalInclusion radical) 1
    rw [goodLineLeviProjection_radical, map_one]
  have tuple : vertices = ![vertices 0, vertices 0, vertices 2] := by
    funext index
    fin_cases index <;> first | rfl | exact repeated
  change realCoefficientComponent degree data.chi real⁻¹ (source vertices (atFinite finite)) = 0
  rw [tuple, sourceCocycle_repeated_first data .plane source cocycle diagonal, map_zero]

theorem goodLineMixedRealCoordinate_projected_zero {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (real : ℝ × ℝ) (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedRealCoordinate degree matrix
      (sourceProjectedRealTranslate data.chi source realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) finite) = 0 := by
  have zero0 : (standardGoodLineRealArgument real).val 0 2 = 0 := by
    rw [standardGoodLineRealArgument_val]
    rfl
  have zero1 : (standardGoodLineRealArgument real).val 1 2 = 0 := by
    rw [standardGoodLineRealArgument_val]
    rfl
  rw [goodLineMixedRealCoordinate_contributions,
    sourceProjectedGoodLine_levi_radical_zero data source cocycle diagonal _ zero0 zero1,
    sourceProjectedGoodLine_levi_radical_zero data source cocycle diagonal _ zero0 zero1,
    sourceProjectedGoodLine_radical_levi_zero data source cocycle diagonal _ zero0 zero1,
    sourceProjectedGoodLine_radical_levi_zero data source cocycle diagonal _ zero0 zero1,
    sub_self, map_zero, map_zero, add_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
