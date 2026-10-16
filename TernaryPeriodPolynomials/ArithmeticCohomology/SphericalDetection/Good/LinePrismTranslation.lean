module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PrismTranslation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismMixed

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineRadicalRealShift (radical : RadicalLattice) (real : ℝ × ℝ) : ℝ × ℝ :=
  (real.1 + 3 * (radical.toAdd.2 : ℝ), real.2 + 3 * (radical.toAdd.1 : ℝ))

theorem standardGoodLineRealArgument_radical (real : ℝ × ℝ) (radical : RadicalLattice) :
    standardGoodLineRealArgument real *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical) =
    standardGoodLineRealArgument (goodLineRadicalRealShift radical real) := by
  apply Units.ext
  change (standardGoodLineRealArgument real).val *
      (lowerRadicalLattice radical).val.map (algebraMap ℚ ℝ) = _
  rw [standardGoodLineRealArgument_val, standardGoodLineRealArgument_val]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [lowerRadicalLattice, lowerPlaneUnipotent, Matrix.mul_apply,
      Fin.sum_univ_three, goodLineRadicalRealShift]

theorem goodLineRealMixedPrimitiveValue_prism_translate {degree : ℕ}
    (character : RankOneCharacter) (source : SourceCochain degree)
    (projection : RealGL3 → RealGL3) (real : RealGL3) (finite : FiniteGL)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    goodLineRealMixedPrimitiveValue
      (sourceRealVertexPrism character source projection real finite) matrix radical =
    (let levi := GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)
     let unipotent := GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)
     let conjugated := GeneralLinearGroup.map (algebraMap ℚ ℝ)
       (lowerRadicalLattice (lowerLeviLatticeInput matrix radical))
     realCoefficientComponent degree character levi
         (sourceRealVertexPrism character source projection (real * levi) finite ![1, conjugated]) -
       realCoefficientComponent degree character unipotent
         (sourceRealVertexPrism character source projection (real * unipotent) finite ![1, levi]) +
       sourceRealVertexPrism character source projection real finite ![1, levi] -
       sourceRealVertexPrism character source projection real finite ![1, unipotent]) := by
  let realMap : RationalGL3 →* RealGL3 := GeneralLinearGroup.map (algebraMap ℚ ℝ)
  have conjugation := congrArg realMap (lowerLeviLatticeInput_conjugation matrix radical)
  rw [map_mul, map_mul] at conjugation
  dsimp only [goodLineRealMixedPrimitiveValue]
  rw [sourceRealVertexPrism_pair_translate character source projection real
    (realMap (arithmeticLevi matrix))]
  rw [sourceRealVertexPrism_pair_translate character source projection real
    (realMap (lowerRadicalLattice radical))]
  rw [conjugation, inv_mul_cancel_left, ← conjugation, inv_mul_cancel_left]

theorem goodLineRealMixedPrimitiveValue_prism_shift {degree : ℕ}
    (character : RankOneCharacter) (source : SourceCochain degree)
    (projection : RealGL3 → RealGL3) (real : ℝ × ℝ) (finite : FiniteGL)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    goodLineRealMixedPrimitiveValue
      (sourceRealVertexPrism character source projection (standardGoodLineRealArgument real) finite)
      matrix radical =
    (let levi := GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)
     let unipotent := GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)
     let conjugated := GeneralLinearGroup.map (algebraMap ℚ ℝ)
       (lowerRadicalLattice (lowerLeviLatticeInput matrix radical))
     realCoefficientComponent degree character levi
         (sourceRealVertexPrism character source projection
           (standardGoodLineRealArgument real * levi) finite ![1, conjugated]) -
       realCoefficientComponent degree character unipotent
         (sourceRealVertexPrism character source projection
           (standardGoodLineRealArgument (goodLineRadicalRealShift radical real)) finite ![1, levi]) +
       sourceRealVertexPrism character source projection
         (standardGoodLineRealArgument real) finite ![1, levi] -
       sourceRealVertexPrism character source projection
         (standardGoodLineRealArgument real) finite ![1, unipotent]) := by
  rw [goodLineRealMixedPrimitiveValue_prism_translate]
  dsimp only
  rw [standardGoodLineRealArgument_radical]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
