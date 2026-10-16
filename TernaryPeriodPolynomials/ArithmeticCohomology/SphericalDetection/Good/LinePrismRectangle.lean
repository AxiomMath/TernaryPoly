module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorRectangleIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismOrbital

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem standardGoodLineRealKernel_contDiff (parameter : ℂ) {order : WithTop ℕ∞} :
    ContDiff ℝ order (standardGoodLineRealKernel parameter) := by
  have base : ContDiff ℝ order (fun real : ℝ × ℝ => 1 + real.1 ^ 2 + real.2 ^ 2) := by fun_prop
  have logarithm := base.log (fun real => ne_of_gt (show 0 < 1 + real.1 ^ 2 + real.2 ^ 2 by positivity))
  unfold standardGoodLineRealKernel
  exact Complex.contDiff_exp.comp
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp logarithm))

theorem goodLineCuspidalPrismRectangleIntegral_exists {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (vertices : Fin 2 → RealGL3) (parameter : ℂ)
    (left₁ right₁ left₂ right₂ : ℝ) (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂) :
    ∃ result : cuspidalTensorValues data.cusp (HomogeneousPoly degree),
      cuspidalTensorHilbertEmbedding data.cusp basis result =
        goodLineCuspidalPrismTruncatedIntegral data basis source cocycle 1 vertices
          (Set.Icc left₁ right₁ ×ˢ Set.Icc left₂ right₂) parameter ∧
      result ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree) := by
  let values (real : ℝ × ℝ) : cuspidalTensorValues data.cusp (HomogeneousPoly degree) :=
    standardGoodLineRealKernel parameter real •
      sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) 1 vertices
  have continuous : Continuous (fun real => cuspidalTensorHilbertEmbedding data.cusp basis (values real)) := by
    simp only [values, map_smul]
    exact (standardGoodLineRealKernel_continuous parameter).smul
      (goodLineCuspidalVertexPrism_hilbertContDiff data trivial basis source cocycle 1 vertices).continuous
  have fixed (real : ℝ × ℝ) :
      values real ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree) :=
    (cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree)).smul_mem _
      (sourceCuspidalVertexPrism_finiteLevel data source cocycle realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) vertices)
  have analytic (center : ℝ × ℝ) : AnalyticAt ℝ
      (fun point : BinaryRealMatrix × (ℝ × ℝ) =>
        binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding data.cusp basis (values point.2))) (1, center) := by
    simp only [values, map_smul]
    exact ((standardGoodLineRealKernel_contDiff parameter (order := ⊤)).contDiffAt.analyticAt.comp
      (f := fun point : BinaryRealMatrix × (ℝ × ℝ) => point.2) (x := (1, center)) analyticAt_snd).smul
        (goodLineCuspidalVertexPrism_orbital_analyticAt data trivial basis source cocycle vertices center)
  simpa only [values, map_smul, goodLineCuspidalPrismTruncatedIntegral] using
    cuspidalTensorRectangleIntegral_exists data.cusp basis values continuous fixed analytic
      left₁ right₁ left₂ right₂ ordered₁ ordered₂

def goodLineCuspidalPrismRectangle {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (left₁ right₁ left₂ right₂ : ℝ)
    (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂)
    (vertices : Fin 2 → RealGL3) : cuspidalTensorValues data.cusp (HomogeneousPoly degree) :=
  (goodLineCuspidalPrismRectangleIntegral_exists data trivial basis source cocycle vertices parameter
    left₁ right₁ left₂ right₂ ordered₁ ordered₂).choose

theorem goodLineCuspidalPrismRectangle_embedding {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (left₁ right₁ left₂ right₂ : ℝ)
    (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂) (vertices : Fin 2 → RealGL3) :
    cuspidalTensorHilbertEmbedding data.cusp basis
        (goodLineCuspidalPrismRectangle data trivial basis source cocycle parameter
          left₁ right₁ left₂ right₂ ordered₁ ordered₂ vertices) =
      goodLineCuspidalPrismTruncatedIntegral data basis source cocycle 1 vertices
        (Set.Icc left₁ right₁ ×ˢ Set.Icc left₂ right₂) parameter :=
  (goodLineCuspidalPrismRectangleIntegral_exists data trivial basis source cocycle vertices parameter
    left₁ right₁ left₂ right₂ ordered₁ ordered₂).choose_spec.1

theorem goodLineCuspidalPrismRectangle_finiteLevel {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (left₁ right₁ left₂ right₂ : ℝ)
    (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂) (vertices : Fin 2 → RealGL3) :
    goodLineCuspidalPrismRectangle data trivial basis source cocycle parameter
        left₁ right₁ left₂ right₂ ordered₁ ordered₂ vertices ∈
      cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree) :=
  (goodLineCuspidalPrismRectangleIntegral_exists data trivial basis source cocycle vertices parameter
    left₁ right₁ left₂ right₂ ordered₁ ordered₂).choose_spec.2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
