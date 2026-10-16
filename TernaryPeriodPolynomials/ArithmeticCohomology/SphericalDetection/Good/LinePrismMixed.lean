module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismKernel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineRealMixedPrimitiveValue {degree : ℕ}
    (primitive : (Fin 2 → RealGL3) → HomogeneousPoly degree)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) : HomogeneousPoly degree :=
  let levi := GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)
  let unipotent := GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)
  primitive ![levi, unipotent * levi] - primitive ![unipotent, unipotent * levi] +
    primitive ![1, levi] - primitive ![1, unipotent]

theorem goodLineRealMixedPrimitiveValue_differential {degree : ℕ}
    (primitive : (Fin 2 → RealGL3) → HomogeneousPoly degree)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    (let vertices := goodLineRealVertices (goodLineLeviSection matrix,
        goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical))
     primitive ![vertices 1, vertices 2] - primitive ![vertices 0, vertices 2] + primitive ![vertices 0, vertices 1]) -
    (let vertices := goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix)
     primitive ![vertices 1, vertices 2] - primitive ![vertices 0, vertices 2] + primitive ![vertices 0, vertices 1]) =
      goodLineRealMixedPrimitiveValue primitive matrix radical := by
  let realMap : RationalGL3 →* RealGL3 := GeneralLinearGroup.map (algebraMap ℚ ℝ)
  have conjugation := congrArg realMap (lowerLeviLatticeInput_conjugation matrix radical)
  rw [map_mul, map_mul] at conjugation
  change (primitive ![realMap (arithmeticLevi matrix),
      realMap (arithmeticLevi matrix * lowerRadicalLattice (lowerLeviLatticeInput matrix radical))] -
    primitive ![realMap 1,
      realMap (arithmeticLevi matrix * lowerRadicalLattice (lowerLeviLatticeInput matrix radical))] +
    primitive ![realMap 1, realMap (arithmeticLevi matrix)]) -
    (primitive ![realMap (lowerRadicalLattice radical), realMap (lowerRadicalLattice radical * arithmeticLevi matrix)] -
    primitive ![realMap 1, realMap (lowerRadicalLattice radical * arithmeticLevi matrix)] +
    primitive ![realMap 1, realMap (lowerRadicalLattice radical)]) = _
  rw [map_one, map_mul, map_mul, ← conjugation]
  dsimp only [goodLineRealMixedPrimitiveValue]
  abel

theorem goodLineMixedRealCoordinate_prism_values {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (real : ℝ × ℝ) (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedRealCoordinate degree matrix
      (sourceRealTranslate data.chi source (standardGoodLineRealArgument real) finite) =
      (let primitive := sourceRealVertexPrism data.chi source realUpperLeftLeviProjection
          (standardGoodLineRealArgument real) finite
       lowerRadicalLatticeContribution degree 0 (goodLineRealMixedPrimitiveValue primitive matrix radicalLatticeFirst) +
         lowerRadicalLatticeContribution degree 1 (goodLineRealMixedPrimitiveValue primitive matrix radicalLatticeSecond)) := by
  rw [goodLineMixedRealCoordinate_source_prism data source cocycle diagonal,
    goodLineMixedRealCoordinate_contributions]
  exact congrArg₂ (fun first second : HomogeneousPoly degree =>
    lowerRadicalLatticeContribution degree 0 first + lowerRadicalLatticeContribution degree 1 second)
      (goodLineRealMixedPrimitiveValue_differential _ matrix radicalLatticeFirst)
      (goodLineRealMixedPrimitiveValue_differential _ matrix radicalLatticeSecond)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
