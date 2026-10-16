module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CompactExponentialIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem standardGoodLineRealKernel_setIntegral_analyticAt
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (values : ℝ × ℝ → E) (continuous : Continuous values)
    (domain : Set (ℝ × ℝ)) (compact : IsCompact domain) (parameter : ℂ) :
    AnalyticAt ℂ (fun parameter => ∫ real in domain,
      standardGoodLineRealKernel parameter real • values real ∂((volume : Measure ℝ).prod volume)) parameter := by
  let height (real : ℝ × ℝ) := Real.log (1 + real.1 ^ 2 + real.2 ^ 2)
  have height_continuous : Continuous height := by
    have base : Continuous (fun real : ℝ × ℝ => 1 + real.1 ^ 2 + real.2 ^ 2) := by fun_prop
    exact base.log (fun real => ne_of_gt (by positivity))
  have analytic := compactSetExponentialIntegral_analyticAt ((volume : Measure ℝ).prod volume)
    height values height_continuous continuous domain compact (-(3 : ℂ) / 4 - parameter / 2)
  have affine : AnalyticAt ℂ (fun value : ℂ => -(3 : ℂ) / 4 - value / 2) parameter := by fun_prop
  exact analytic.comp (f := fun value : ℂ => -(3 : ℂ) / 4 - value / 2) (x := parameter) affine

def goodLineCuspidalPrismTruncatedIntegral {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (base : AdelicGL) (vertices : Fin 2 → RealGL3) (domain : Set (ℝ × ℝ))
    (parameter : ℂ) : index → data.cusp.H :=
  ∫ real in domain, standardGoodLineRealKernel parameter real •
    cuspidalTensorHilbertEmbedding data.cusp basis
      (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) base vertices) ∂((volume : Measure ℝ).prod volume)

theorem goodLineCuspidalPrismTruncatedIntegral_analyticAt {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (base : AdelicGL) (vertices : Fin 2 → RealGL3) (domain : Set (ℝ × ℝ))
    (compact : IsCompact domain) (parameter : ℂ) :
    AnalyticAt ℂ (goodLineCuspidalPrismTruncatedIntegral data basis source cocycle base vertices domain) parameter :=
  standardGoodLineRealKernel_setIntegral_analyticAt _
    (goodLineCuspidalVertexPrism_hilbertContDiff data trivial basis source cocycle base vertices).continuous
    domain compact parameter

theorem goodLineCuspidalPrismTruncatedIntegral_endpoint {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (base : AdelicGL) (vertices : Fin 2 → RealGL3) (domain : Set (ℝ × ℝ)) :
    goodLineCuspidalPrismTruncatedIntegral data basis source cocycle base vertices domain cohomologicalPoint =
    ∫ real in domain, cuspidalTensorHilbertEmbedding data.cusp basis
      (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) base vertices) ∂((volume : Measure ℝ).prod volume) := by
  simp only [goodLineCuspidalPrismTruncatedIntegral, standardGoodLineRealKernel_endpoint, one_smul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
