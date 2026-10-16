module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalPrismDifferential

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineCuspidalMixedPrimitiveValue {degree : ℕ} (cusp : CuspidalRepresentation)
    (primitive : (Fin 2 → RealGL3) → cuspidalTensorValues cusp (HomogeneousPoly degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    cuspidalTensorValues cusp (HomogeneousPoly degree) :=
  let levi := GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)
  let unipotent := GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)
  primitive ![levi, unipotent * levi] - primitive ![unipotent, unipotent * levi] +
    primitive ![1, levi] - primitive ![1, unipotent]

theorem sourceCuspidalVertexPrism_goodLine_mixed {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (real : ℝ × ℝ) (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    sourcePlaneCuspidalValues data source cocycle
        (goodLineRealVertices (goodLineLeviSection matrix,
          goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical)))
        (atInfinity (standardGoodLineRealArgument real)) -
      sourcePlaneCuspidalValues data source cocycle
        (goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix))
        (atInfinity (standardGoodLineRealArgument real)) =
    goodLineCuspidalMixedPrimitiveValue data.cusp
      (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) 1) matrix radical := by
  let : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly degree)).addCommGroup
  let first := goodLineRealVertices (goodLineLeviSection matrix,
    goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical))
  let second := goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix)
  let projected (vertices : Fin 3 → RealGL3) (index : Fin 3) :=
    realUpperLeftLeviProjection (standardGoodLineRealArgument real * vertices index)
  have zero0 : (standardGoodLineRealArgument real).val 0 2 = 0 := by
    rw [standardGoodLineRealArgument_val]
    rfl
  have zero1 : (standardGoodLineRealArgument real).val 1 2 = 0 := by
    rw [standardGoodLineRealArgument_val]
    rfl
  have first_repeated : projected first 2 = projected first 1 := by
    apply realUpperLeftLeviProjection_goodLine_congr (standardGoodLineRealArgument real) zero0 zero1
      (goodLineLeviSection matrix * goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical))
      (goodLineLeviSection matrix)
    rw [map_mul, goodLineLeviProjection_radical, mul_one]
  have second_repeated : projected second 1 = projected second 0 := by
    apply realUpperLeftLeviProjection_goodLine_congr (standardGoodLineRealArgument real) zero0 zero1
      (goodLineRadicalInclusion radical) 1
    rw [goodLineLeviProjection_radical, map_one]
  have first_zero : sourcePlaneCuspidalValues data source cocycle (projected first) 1 = 0 := by
    have tuple : projected first = ![projected first 0, projected first 1, projected first 1] := by
      funext index
      fin_cases index <;> first | rfl | exact first_repeated
    rw [tuple, sourcePlaneCuspidalValues_repeated_last data source cocycle diagonal]
  have second_zero : sourcePlaneCuspidalValues data source cocycle (projected second) 1 = 0 := by
    have tuple : projected second = ![projected second 0, projected second 0, projected second 2] := by
      funext index
      fin_cases index <;> first | rfl | exact second_repeated
    rw [tuple, sourcePlaneCuspidalValues_repeated_first data source cocycle diagonal]
  have first_differential := sourceCuspidalVertexPrism_differential data source cocycle
    realUpperLeftLeviProjection (standardGoodLineRealArgument real) 1 first
  have second_differential := sourceCuspidalVertexPrism_differential data source cocycle
    realUpperLeftLeviProjection (standardGoodLineRealArgument real) 1 second
  change sourceCuspidalRealTranslate data source cocycle (standardGoodLineRealArgument real) 1 first -
    cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi (standardGoodLineRealArgument real)⁻¹)
      (sourcePlaneCuspidalValues data source cocycle (projected first) 1) = _ at first_differential
  change sourceCuspidalRealTranslate data source cocycle (standardGoodLineRealArgument real) 1 second -
    cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi (standardGoodLineRealArgument real)⁻¹)
      (sourcePlaneCuspidalValues data source cocycle (projected second) 1) = _ at second_differential
  simp only [first_zero, map_zero, sub_zero, sourceCuspidalRealTranslate_atInfinity] at first_differential
  simp only [second_zero, map_zero, sub_zero, sourceCuspidalRealTranslate_atInfinity] at second_differential
  change sourcePlaneCuspidalValues data source cocycle first (atInfinity (standardGoodLineRealArgument real)) -
    sourcePlaneCuspidalValues data source cocycle second (atInfinity (standardGoodLineRealArgument real)) = _
  rw [first_differential, second_differential]
  apply Subtype.ext
  funext argument
  exact goodLineRealMixedPrimitiveValue_differential
    (fun vertices => (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
      (standardGoodLineRealArgument real) 1 vertices).val argument) matrix radical

/-- The actual cuspidal tensor in the finite standard average is the mixed prism value. -/
theorem goodLineMixedCuspidalValues_prism {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (real : ℝ × ℝ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedCuspidalValues data source cocycle matrix (atInfinity (standardGoodLineRealArgument real)) =
    (let primitive := sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) 1
     cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 0)
         (goodLineCuspidalMixedPrimitiveValue data.cusp primitive matrix radicalLatticeFirst) +
       cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 1)
         (goodLineCuspidalMixedPrimitiveValue data.cusp primitive matrix radicalLatticeSecond)) := by
  rw [goodLineMixedCuspidalValues, sourceCuspidalVertexPrism_goodLine_mixed data source cocycle diagonal,
    sourceCuspidalVertexPrism_goodLine_mixed data source cocycle diagonal]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
