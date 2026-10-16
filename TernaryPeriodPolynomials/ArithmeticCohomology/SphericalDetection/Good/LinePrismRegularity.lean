module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PrismRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realUpperLeftLeviProjection_standardGoodLine_mul (real : ℝ × ℝ) (vertex : RealGL3) :
    realUpperLeftLeviProjection (standardGoodLineRealArgument real * vertex) =
      realUpperLeftLeviProjection (standardGoodLineRealArgument 0 * vertex) := by
  apply congrArg (fun block => planeLevi (invertibleMatrix block) 1)
  change upperLeftBlock ((standardGoodLineRealArgument real).val * vertex.val) =
    upperLeftBlock ((standardGoodLineRealArgument 0).val * vertex.val)
  rw [standardGoodLineRealArgument_val, standardGoodLineRealArgument_val]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [upperLeftBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem goodLineCuspidalVertexPrism_hilbertContDiff {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (base : AdelicGL) (vertices : Fin 2 → RealGL3) :
    ContDiff ℝ ⊤ (fun real : ℝ × ℝ => cuspidalTensorHilbertEmbedding data.cusp basis
      (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) base vertices)) := by
  apply sourceCuspidalVertexPrism_hilbertContDiff data basis source cocycle
    realUpperLeftLeviProjection standardGoodLineRealArgument base (fun _ => vertices)
  · apply contDiff_pi.mpr
    intro index
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    change ContDiff ℝ ⊤ (fun real : ℝ × ℝ =>
      ∑ middle, (standardGoodLineRealArgument real).val row middle * (vertices index).val middle column)
    apply ContDiff.sum
    intro middle _
    exact (contDiff_pi.mp (contDiff_pi.mp standardGoodLineRealArgument_contDiff row) middle).mul contDiff_const
  · simp only [realUpperLeftLeviProjection_standardGoodLine_mul]
    exact contDiff_const
  · intro polynomial functional
    rw [trivial]
    exact standardGoodLineRealCoefficient_functional_contDiff polynomial functional

theorem goodLineCuspidalVertexPrism_integrableOn_compact {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (base : AdelicGL) (vertices : Fin 2 → RealGL3) (parameter : ℂ)
    (domain : Set (ℝ × ℝ)) (compact : IsCompact domain) :
    IntegrableOn (fun real : ℝ × ℝ => standardGoodLineRealKernel parameter real •
      cuspidalTensorHilbertEmbedding data.cusp basis
        (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
          (standardGoodLineRealArgument real) base vertices)) domain ((volume : Measure ℝ).prod volume) := by
  have continuous := (standardGoodLineRealKernel_continuous parameter).smul
    (goodLineCuspidalVertexPrism_hilbertContDiff data trivial basis source cocycle base vertices).continuous
  exact continuous.continuousOn.integrableOn_compact compact

theorem goodLineCuspidalVertexPrism_radicalShift_integrableOn_compact {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (base : AdelicGL) (vertices : Fin 2 → RealGL3) (parameter : ℂ) (radical : RadicalLattice)
    (domain : Set (ℝ × ℝ)) (compact : IsCompact domain) :
    IntegrableOn (fun real : ℝ × ℝ => standardGoodLineRealKernel parameter real •
      cuspidalTensorHilbertEmbedding data.cusp basis
        (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
          (standardGoodLineRealArgument (goodLineRadicalRealShift radical real)) base vertices))
      domain ((volume : Measure ℝ).prod volume) := by
  have shift_continuous : Continuous (goodLineRadicalRealShift radical) := by
    unfold goodLineRadicalRealShift
    fun_prop
  have continuous := (standardGoodLineRealKernel_continuous parameter).smul
    ((goodLineCuspidalVertexPrism_hilbertContDiff data trivial basis source cocycle base vertices).continuous.comp
      shift_continuous)
  exact continuous.continuousOn.integrableOn_compact compact

end TernaryPeriodPolynomials.SphericalDetection.Helpers
