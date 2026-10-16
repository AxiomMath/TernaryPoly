module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Local.BinaryTriangularCosets

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineLeviRealInput (matrix : GeneralLinearGroup (Fin 2) ℤ) (real : ℝ × ℝ) : ℝ × ℝ :=
  (real.2 * (matrix.val 0 1 : ℝ) + real.1 * (matrix.val 1 1 : ℝ),
    real.2 * (matrix.val 0 0 : ℝ) + real.1 * (matrix.val 1 0 : ℝ))

def goodLineConjugateRealLevi (matrix : GeneralLinearGroup (Fin 2) ℤ) : RealGL3 :=
  planeLevi (binaryPivotSwap * GeneralLinearGroup.map (Int.castRingHom ℝ) matrix * binaryPivotSwap) 1

theorem standardGoodLineRealArgument_levi (real : ℝ × ℝ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    standardGoodLineRealArgument real *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix) =
    goodLineConjugateRealLevi matrix * standardGoodLineRealArgument (goodLineLeviRealInput matrix real) := by
  apply Units.ext
  change (standardGoodLineRealArgument real).val *
      (arithmeticLevi matrix).val.map (algebraMap ℚ ℝ) =
    (goodLineConjugateRealLevi matrix).val * (standardGoodLineRealArgument _).val
  rw [standardGoodLineRealArgument_val, standardGoodLineRealArgument_val]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [goodLineConjugateRealLevi, arithmeticLevi, planeLevi, planeBlock,
      binaryPivotSwap, goodLineLeviRealInput, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three, Fin.sum_univ_two]

theorem goodLineLeviRealInput_shift (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (radical : RadicalLattice) (real : ℝ × ℝ) :
    goodLineLeviRealInput matrix (goodLineRadicalRealShift radical real) =
    goodLineRadicalRealShift (lowerLeviLatticeInput matrix radical) (goodLineLeviRealInput matrix real) := by
  ext <;> simp [goodLineLeviRealInput, goodLineRadicalRealShift, lowerLeviLatticeInput] <;> ring

theorem realUpperLeftLeviProjection_standardGoodLine (real : ℝ × ℝ) :
    realUpperLeftLeviProjection (standardGoodLineRealArgument real) =
      planeLevi (binaryPivotSwap : BinaryRealGL) 1 := by
  have block : upperLeftBlock (standardGoodLineRealArgument real).val =
      (binaryPivotSwap : BinaryRealGL).val := by
    rw [standardGoodLineRealArgument_val]
    funext row column
    fin_cases row <;> fin_cases column <;> rfl
  rw [realUpperLeftLeviProjection, block, invertibleMatrix_coe]

theorem realUpperLeftLeviProjection_standardGoodLine_levi (real : ℝ × ℝ)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    realUpperLeftLeviProjection (standardGoodLineRealArgument real *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)) =
    planeLevi (binaryPivotSwap * GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) 1 := by
  have block : upperLeftBlock (standardGoodLineRealArgument real *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)).val =
      (binaryPivotSwap * GeneralLinearGroup.map (Int.castRingHom ℝ) matrix).val := by
    change upperLeftBlock ((standardGoodLineRealArgument real).val *
      (arithmeticLevi matrix).val.map (algebraMap ℚ ℝ)) = _
    rw [standardGoodLineRealArgument_val]
    funext row column
    fin_cases row <;> fin_cases column <;>
      simp [upperLeftBlock, arithmeticLevi, planeLevi, planeBlock, binaryPivotSwap,
        Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  rw [realUpperLeftLeviProjection, block, invertibleMatrix_coe]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
