module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismLevi

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realUpperLeftLeviProjection_standardGoodLine_radical (real : ℝ × ℝ) (radical : RadicalLattice) :
    realUpperLeftLeviProjection (standardGoodLineRealArgument real *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)) =
    planeLevi (binaryPivotSwap : BinaryRealGL) 1 := by
  rw [standardGoodLineRealArgument_radical, realUpperLeftLeviProjection_standardGoodLine]

def goodLineRadicalPrism {degree : ℕ} (character : RankOneCharacter)
    (source : SourceCochain degree) (real : ℝ × ℝ) (finite : FiniteGL)
    (radical : RadicalLattice) : HomogeneousPoly degree :=
  sourceRealVertexPrism character source realUpperLeftLeviProjection
    (standardGoodLineRealArgument real) finite
    ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)]

theorem goodLineRadicalPrism_value {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (real : ℝ × ℝ) (finite : FiniteGL) (radical : RadicalLattice) :
    goodLineRadicalPrism data.chi source real finite radical =
    realCoefficientComponent degree data.chi (standardGoodLineRealArgument real)⁻¹
      (source ![planeLevi (binaryPivotSwap : BinaryRealGL) 1,
        standardGoodLineRealArgument real,
        standardGoodLineRealArgument (goodLineRadicalRealShift radical real)] (atFinite finite)) := by
  change realCoefficientComponent degree data.chi (standardGoodLineRealArgument real)⁻¹
    (source ![realUpperLeftLeviProjection (standardGoodLineRealArgument real * 1),
        standardGoodLineRealArgument real * 1,
        standardGoodLineRealArgument real * GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)]
        (atFinite finite) -
      source ![realUpperLeftLeviProjection (standardGoodLineRealArgument real * 1),
        realUpperLeftLeviProjection (standardGoodLineRealArgument real *
          GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)),
        standardGoodLineRealArgument real * GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)]
        (atFinite finite)) = _
  rw [mul_one, realUpperLeftLeviProjection_standardGoodLine,
    realUpperLeftLeviProjection_standardGoodLine_radical, standardGoodLineRealArgument_radical,
    sourceCocycle_repeated_first data .plane source cocycle diagonal, sub_zero]

theorem goodLineRadicalPrism_one {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (real : ℝ × ℝ) (finite : FiniteGL) :
    goodLineRadicalPrism data.chi source real finite 1 = 0 := by
  rw [goodLineRadicalPrism_value data source cocycle diagonal, goodLineRadicalRealShift_one,
    sourceCocycle_repeated_last data .plane source cocycle diagonal, map_zero]

theorem goodLineRadicalPrism_at_zero {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (finite : FiniteGL) (radical : RadicalLattice) :
    goodLineRadicalPrism data.chi source 0 finite radical = 0 := by
  have at_zero : standardGoodLineRealArgument 0 = planeLevi (binaryPivotSwap : BinaryRealGL) 1 := by
    apply Units.ext
    rw [standardGoodLineRealArgument_val]
    rfl
  rw [goodLineRadicalPrism_value data source cocycle diagonal, at_zero,
    sourceCocycle_repeated_first data .plane source cocycle diagonal, map_zero]

/-- On radical pairs the source is the differential for the translated primitive family. -/
theorem goodLineRadicalPrism_differential {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (real : ℝ × ℝ) (finite : FiniteGL) (first second : RadicalLattice) :
    sourceRealTranslate data.chi source (standardGoodLineRealArgument real) finite
      ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice first),
        GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice (first * second))] =
    realCoefficientComponent degree data.chi
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice first))
        (goodLineRadicalPrism data.chi source (goodLineRadicalRealShift first real) finite second) -
      goodLineRadicalPrism data.chi source real finite (first * second) +
      goodLineRadicalPrism data.chi source real finite first := by
  let radicalMap : RadicalLattice →* RealGL3 :=
    (GeneralLinearGroup.map (algebraMap ℚ ℝ)).comp lowerRadicalLattice
  let vertices : Fin 3 → RealGL3 := ![1, radicalMap first, radicalMap (first * second)]
  have projected_vertices : (fun index => realUpperLeftLeviProjection
      (standardGoodLineRealArgument real * vertices index)) =
      fun _ => planeLevi (binaryPivotSwap : BinaryRealGL) 1 := by
    funext index
    fin_cases index
    · change realUpperLeftLeviProjection (standardGoodLineRealArgument real * 1) = _
      rw [mul_one, realUpperLeftLeviProjection_standardGoodLine]
    · exact realUpperLeftLeviProjection_standardGoodLine_radical real first
    · exact realUpperLeftLeviProjection_standardGoodLine_radical real (first * second)
  have projected_zero : sourceProjectedRealTranslate data.chi source realUpperLeftLeviProjection
      (standardGoodLineRealArgument real) finite vertices = 0 := by
    rw [sourceProjectedRealTranslate, projected_vertices, diagonal, map_zero]
  have differential := sourceRealTranslate_prism data .plane source cocycle realUpperLeftLeviProjection
    (standardGoodLineRealArgument real) finite vertices
  rw [projected_zero, sub_zero] at differential
  change sourceRealTranslate data.chi source (standardGoodLineRealArgument real) finite vertices = _
  rw [differential]
  change sourceRealVertexPrism data.chi source realUpperLeftLeviProjection
      (standardGoodLineRealArgument real) finite ![radicalMap first, radicalMap (first * second)] -
    goodLineRadicalPrism data.chi source real finite (first * second) +
    goodLineRadicalPrism data.chi source real finite first = _
  rw [sourceRealVertexPrism_pair_translate, map_mul radicalMap, inv_mul_cancel_left]
  dsimp only [radicalMap, MonoidHom.comp_apply]
  rw [standardGoodLineRealArgument_radical]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
