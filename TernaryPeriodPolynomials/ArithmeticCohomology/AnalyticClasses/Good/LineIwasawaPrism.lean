module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineGramSchmidt
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineCuspidalPrism
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineMixedCuspidalValues

@[expose] public section


/-!
# The good-line mixed cusp values through the Iwasawa vertex map

The codexiom prism decomposition of the good-line mixed cusp values used the upper-left Levi
projection, for which the projected simplices degenerate and the whole mixed value is a prism term
of unbounded shape. Here the same decomposition is made with the plane-equivariant Gram–Schmidt
vertex map `gsVertex`, which moves every vertex by an orthogonal matrix. The mixed value splits as

* the *projected part*: the source on the projected simplices, which lie in the plane parabolic on
  the big cell, and
* the *prism part*: the mixed coordinate of the prism one-cochain of `gsVertex`, whose simplices
  `(φ y₀, y₀, y₁)` and `(φ y₀, φ y₁, y₁)` have bounded shape.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The projected part of one radical contribution: the source on the Gram–Schmidt projected
simplices, transported back by the real good-line argument. -/
def goodLineIwasawaProjectedTerm (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (real : ℝ × ℝ)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    cuspidalTensorValues data.cusp (HomogeneousPoly n) :=
  cuspidalTensorMap data.cusp (realCoefficientComponent n data.chi (standardGoodLineRealArgument real)⁻¹)
      (sourcePlaneCuspidalValues data source cocycle
        (fun index => gsVertex (standardGoodLineRealArgument real *
          goodLineRealVertices (goodLineLeviSection matrix,
            goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical)) index)) 1) -
    cuspidalTensorMap data.cusp (realCoefficientComponent n data.chi (standardGoodLineRealArgument real)⁻¹)
      (sourcePlaneCuspidalValues data source cocycle
        (fun index => gsVertex (standardGoodLineRealArgument real *
          goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix) index)) 1)

/-- The prism one-cochain of the Gram–Schmidt vertex map at the real good-line argument. -/
def goodLineIwasawaPrism (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (real : ℝ × ℝ) :
    (Fin 2 → RealGL3) → cuspidalTensorValues data.cusp (HomogeneousPoly n) :=
  sourceCuspidalVertexPrism data source cocycle gsVertex (standardGoodLineRealArgument real) 1

/-- The prism decomposition of a difference of two simplices. -/
theorem sourcePlaneCuspidalValues_sub_iwasawa (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (real : ℝ × ℝ) (first second : Fin 3 → RealGL3) :
    sourcePlaneCuspidalValues data source cocycle first (atInfinity (standardGoodLineRealArgument real)) -
      sourcePlaneCuspidalValues data source cocycle second (atInfinity (standardGoodLineRealArgument real)) =
    (cuspidalTensorMap data.cusp (realCoefficientComponent n data.chi (standardGoodLineRealArgument real)⁻¹)
        (sourcePlaneCuspidalValues data source cocycle
            (fun index => gsVertex (standardGoodLineRealArgument real * first index)) 1) -
      cuspidalTensorMap data.cusp (realCoefficientComponent n data.chi (standardGoodLineRealArgument real)⁻¹)
        (sourcePlaneCuspidalValues data source cocycle
            (fun index => gsVertex (standardGoodLineRealArgument real * second index)) 1)) +
      ((goodLineIwasawaPrism data source cocycle real ![first 1, first 2] -
          goodLineIwasawaPrism data source cocycle real ![first 0, first 2] +
          goodLineIwasawaPrism data source cocycle real ![first 0, first 1]) -
        (goodLineIwasawaPrism data source cocycle real ![second 1, second 2] -
          goodLineIwasawaPrism data source cocycle real ![second 0, second 2] +
          goodLineIwasawaPrism data source cocycle real ![second 0, second 1])) := by
  have first_differential := sourceCuspidalVertexPrism_differential data source cocycle
    gsVertex (standardGoodLineRealArgument real) 1 first
  have second_differential := sourceCuspidalVertexPrism_differential data source cocycle
    gsVertex (standardGoodLineRealArgument real) 1 second
  rw [sourceCuspidalRealTranslate_atInfinity] at first_differential second_differential
  simp only [goodLineIwasawaPrism]
  rw [← first_differential, ← second_differential]
  let : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly n)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly n)).addCommGroup
  abel

/-- **Iwasawa prism decomposition of one radical contribution.** -/
theorem goodLineMixedRadicalTerm_iwasawa (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (real : ℝ × ℝ)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    sourcePlaneCuspidalValues data source cocycle
        (goodLineRealVertices (goodLineLeviSection matrix,
          goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical)))
        (atInfinity (standardGoodLineRealArgument real)) -
      sourcePlaneCuspidalValues data source cocycle
        (goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix))
        (atInfinity (standardGoodLineRealArgument real)) =
    goodLineIwasawaProjectedTerm data source cocycle real matrix radical +
      goodLineCuspidalMixedPrimitiveValue data.cusp
        (goodLineIwasawaPrism data source cocycle real) matrix radical := by
  set P := goodLineIwasawaPrism data source cocycle real with hP
  set first := goodLineRealVertices (goodLineLeviSection matrix,
    goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical)) with hfirst
  set second := goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix) with hsecond
  have key : (P ![first 1, first 2] - P ![first 0, first 2] + P ![first 0, first 1]) -
      (P ![second 1, second 2] - P ![second 0, second 2] + P ![second 0, second 1]) =
      goodLineCuspidalMixedPrimitiveValue data.cusp P matrix radical := by
    apply Subtype.ext
    funext argument
    exact goodLineRealMixedPrimitiveValue_differential
      (fun vertices => (P vertices).val argument) matrix radical
  rw [sourcePlaneCuspidalValues_sub_iwasawa, hP, key]
  rfl

/-- **Iwasawa prism decomposition of the good-line mixed cusp values.** -/
theorem goodLineMixedCuspidalValues_iwasawa (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (real : ℝ × ℝ)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedCuspidalValues data source cocycle matrix (atInfinity (standardGoodLineRealArgument real)) =
      (cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution n 0)
          (goodLineIwasawaProjectedTerm data source cocycle real matrix radicalLatticeFirst) +
        cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution n 1)
          (goodLineIwasawaProjectedTerm data source cocycle real matrix radicalLatticeSecond)) +
      (cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution n 0)
          (goodLineCuspidalMixedPrimitiveValue data.cusp
            (goodLineIwasawaPrism data source cocycle real) matrix radicalLatticeFirst) +
        cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution n 1)
          (goodLineCuspidalMixedPrimitiveValue data.cusp
            (goodLineIwasawaPrism data source cocycle real) matrix radicalLatticeSecond)) := by
  rw [goodLineMixedCuspidalValues, goodLineMixedRadicalTerm_iwasawa, goodLineMixedRadicalTerm_iwasawa,
    map_add, map_add]
  abel

end TernaryPeriodPolynomials.AnalyticClasses
