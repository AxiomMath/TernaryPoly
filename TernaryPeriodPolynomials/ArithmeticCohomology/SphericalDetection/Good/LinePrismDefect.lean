module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineKernelShift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem lowerRadicalLatticeContribution_boundary (degree : ℕ) (positive : 0 < degree)
    (polynomial : HomogeneousPoly degree) :
    lowerRadicalLatticeContribution degree 0
        (realCoefficientComponent degree trivialCharacter
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radicalLatticeFirst)) polynomial - polynomial) +
      lowerRadicalLatticeContribution degree 1
        (realCoefficientComponent degree trivialCharacter
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radicalLatticeSecond)) polynomial - polynomial) = 0 := by
  have zero := lowerRadicalCocycleCoordinate_oneBoundary degree positive polynomial
  rw [lowerRadicalCocycleCoordinate_value] at zero
  change lowerRadicalCoordinate degree (fun coordinate =>
    (lowerRadicalAverageEquiv degree coordinate).symm
      (realCoefficientComponent degree trivialCharacter
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice (radicalLatticeGenerator coordinate)))
          polynomial - polynomial)) = 0 at zero
  rw [lowerRadicalCoordinate_averages] at zero
  exact zero

def goodLinePrismRadicalTerm {degree : ℕ} (character : RankOneCharacter)
    (source : SourceCochain degree) (real : ℝ × ℝ) (finite : FiniteGL)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) : HomogeneousPoly degree :=
  let levi := GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)
  let unipotent := GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)
  let conjugated := GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (lowerRadicalLattice (lowerLeviLatticeInput matrix radical))
  realCoefficientComponent degree character levi
      (sourceRealVertexPrism character source realUpperLeftLeviProjection
        (standardGoodLineRealArgument real * levi) finite ![1, conjugated]) -
    sourceRealVertexPrism character source realUpperLeftLeviProjection
      (standardGoodLineRealArgument real) finite ![1, unipotent]

def goodLinePrismShiftTerm {degree : ℕ} (character : RankOneCharacter)
    (source : SourceCochain degree) (real : ℝ × ℝ) (finite : FiniteGL)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) : HomogeneousPoly degree :=
  let levi := GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)
  let unipotent := GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)
  realCoefficientComponent degree character unipotent
    (sourceRealVertexPrism character source realUpperLeftLeviProjection
        (standardGoodLineRealArgument (goodLineRadicalRealShift radical real)) finite ![1, levi] -
      sourceRealVertexPrism character source realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) finite ![1, levi])

theorem goodLineRealMixedPrimitiveValue_prism_defect {degree : ℕ}
    (character : RankOneCharacter) (source : SourceCochain degree)
    (real : ℝ × ℝ) (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (radical : RadicalLattice) :
    goodLineRealMixedPrimitiveValue
      (sourceRealVertexPrism character source realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) finite) matrix radical =
    goodLinePrismRadicalTerm character source real finite matrix radical -
      goodLinePrismShiftTerm character source real finite matrix radical -
      (realCoefficientComponent degree character
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical))
          (sourceRealVertexPrism character source realUpperLeftLeviProjection
            (standardGoodLineRealArgument real) finite
            ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)]) -
        sourceRealVertexPrism character source realUpperLeftLeviProjection
          (standardGoodLineRealArgument real) finite
          ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)]) := by
  rw [goodLineRealMixedPrimitiveValue_prism_shift]
  dsimp only [goodLinePrismRadicalTerm, goodLinePrismShiftTerm]
  rw [map_sub]
  abel

/-- The common polynomial boundary cancels before integrating any prism term. -/
theorem goodLineMixedRealCoordinate_prism_defect {degree : ℕ} (positive : 0 < degree)
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (real : ℝ × ℝ) (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedRealCoordinate degree matrix
      (sourceRealTranslate data.chi source (standardGoodLineRealArgument real) finite) =
    (lowerRadicalLatticeContribution degree 0
        (goodLinePrismRadicalTerm data.chi source real finite matrix radicalLatticeFirst) +
      lowerRadicalLatticeContribution degree 1
        (goodLinePrismRadicalTerm data.chi source real finite matrix radicalLatticeSecond)) -
    (lowerRadicalLatticeContribution degree 0
        (goodLinePrismShiftTerm data.chi source real finite matrix radicalLatticeFirst) +
      lowerRadicalLatticeContribution degree 1
        (goodLinePrismShiftTerm data.chi source real finite matrix radicalLatticeSecond)) := by
  rw [goodLineMixedRealCoordinate_prism_values data source cocycle diagonal]
  dsimp only
  rw [goodLineRealMixedPrimitiveValue_prism_defect, goodLineRealMixedPrimitiveValue_prism_defect]
  simp only [map_sub]
  have boundary := lowerRadicalLatticeContribution_boundary degree positive
    (sourceRealVertexPrism data.chi source realUpperLeftLeviProjection
      (standardGoodLineRealArgument real) finite
      ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)])
  rw [← trivial] at boundary
  simp only [map_sub] at boundary
  linear_combination (norm := abel) -boundary

end TernaryPeriodPolynomials.SphericalDetection.Helpers
