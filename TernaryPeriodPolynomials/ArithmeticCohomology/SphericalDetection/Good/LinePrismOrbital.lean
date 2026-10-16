module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineCuspidalPrism
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalOrbitalAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.AnalyticRadicalAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourceCuspidalVertexPrism_finiteLevel {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (projection : RealGL3 → RealGL3) (real : RealGL3) (vertices : Fin 2 → RealGL3) :
    sourceCuspidalVertexPrism data source cocycle projection real 1 vertices ∈
      cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree) := by
  have fixed (vertices : Fin 3 → RealGL3) :
      sourcePlaneCuspidalValues data source cocycle vertices 1 ∈
      cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree) := by
    simpa only [atInfinity_one] using sourcePlaneCuspidalValues_finiteLevel data source cocycle vertices 1
  intro integral argument
  change realCoefficientComponent degree data.chi real⁻¹
      ((sourcePlaneCuspidalValues data source cocycle
          ![projection (real * vertices 0), real * vertices 0, real * vertices 1] 1).val
          (argument * atFinite (GeneralLinearGroup.map integralEmbedding integral)) -
        (sourcePlaneCuspidalValues data source cocycle
          ![projection (real * vertices 0), projection (real * vertices 1), real * vertices 1] 1).val
          (argument * atFinite (GeneralLinearGroup.map integralEmbedding integral))) =
    realCoefficientComponent degree data.chi real⁻¹
      ((sourcePlaneCuspidalValues data source cocycle
          ![projection (real * vertices 0), real * vertices 0, real * vertices 1] 1).val argument -
        (sourcePlaneCuspidalValues data source cocycle
          ![projection (real * vertices 0), projection (real * vertices 1), real * vertices 1] 1).val argument)
  rw [fixed _ integral argument, fixed _ integral argument]

theorem goodLineCuspidalVertexPrism_orbital_analyticAt {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (vertices : Fin 2 → RealGL3) (center : ℝ × ℝ) :
    AnalyticAt ℝ (fun point : BinaryRealMatrix × (ℝ × ℝ) =>
      binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding data.cusp basis
          (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
            (standardGoodLineRealArgument point.2) 1 vertices))) (1, center) := by
  let first (real : ℝ × ℝ) : Fin 3 → RealGL3 :=
    ![realUpperLeftLeviProjection (standardGoodLineRealArgument real * vertices 0),
      standardGoodLineRealArgument real * vertices 0, standardGoodLineRealArgument real * vertices 1]
  let second (real : ℝ × ℝ) : Fin 3 → RealGL3 :=
    ![realUpperLeftLeviProjection (standardGoodLineRealArgument real * vertices 0),
      realUpperLeftLeviProjection (standardGoodLineRealArgument real * vertices 1),
      standardGoodLineRealArgument real * vertices 1]
  have product_regular (vertex : RealGL3) :
      ContDiff ℝ ⊤ (fun real : ℝ × ℝ => (standardGoodLineRealArgument real * vertex).val) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    change ContDiff ℝ ⊤ (fun real : ℝ × ℝ =>
      ∑ middle, (standardGoodLineRealArgument real).val row middle * vertex.val middle column)
    exact ContDiff.sum (fun middle _ =>
      (contDiff_pi.mp (contDiff_pi.mp standardGoodLineRealArgument_contDiff row) middle).mul contDiff_const)
  have projected_regular (vertex : RealGL3) : ContDiff ℝ ⊤ (fun real : ℝ × ℝ =>
      (realUpperLeftLeviProjection (standardGoodLineRealArgument real * vertex)).val) := by
    simp only [realUpperLeftLeviProjection_standardGoodLine_mul]
    exact contDiff_const
  have first_regular : ContDiff ℝ ⊤ (fun real index => (first real index).val) := by
    apply contDiff_pi.mpr
    intro position
    fin_cases position
    · exact projected_regular _
    · exact product_regular _
    · exact product_regular _
  have second_regular : ContDiff ℝ ⊤ (fun real index => (second real index).val) := by
    apply contDiff_pi.mpr
    intro position
    fin_cases position
    · exact projected_regular _
    · exact projected_regular _
    · exact product_regular _
  have first_analytic := sourcePlaneCuspidalValues_orbital_analyticAt data basis source cocycle first center first_regular.contDiffAt
  have second_analytic := sourcePlaneCuspidalValues_orbital_analyticAt data basis source cocycle second center second_regular.contDiffAt
  have raw_regular := (first_analytic.sub second_analytic).contDiffAt (n := ⊤)
  apply ContDiffAt.analyticAt
  simp only [sourceCuspidalVertexPrism, cuspidalTensorHilbertEmbedding_map,
    basisHilbertCoefficient_translation]
  apply contDiffAt_pi.mpr
  intro position
  simp only [basisHilbertCoefficient_apply]
  apply ContDiffAt.sum
  intro source_index _
  have coefficient := (standardGoodLineRealCoefficient_functional_contDiff
    (basis source_index) (basis.coord position) (order := ⊤)).contDiffAt.comp
      (f := fun point : BinaryRealMatrix × (ℝ × ℝ) => point.2) (1, center) contDiffAt_snd
  rw [trivial]
  apply coefficient.smul
  simpa only [homogeneousVertexPrism, map_sub, Pi.sub_apply, first, second] using
    contDiffAt_pi.mp raw_regular source_index

end TernaryPeriodPolynomials.SphericalDetection.Helpers
