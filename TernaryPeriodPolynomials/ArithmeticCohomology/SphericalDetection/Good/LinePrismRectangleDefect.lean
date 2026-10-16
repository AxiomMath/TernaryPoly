module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalPrismTranslation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineCuspidalPrismRectangleDefect {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (left₁ right₁ left₂ right₂ : ℝ)
    (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂)
    (radical : RadicalLattice) (vertices : Fin 2 → RealGL3) :
    cuspidalTensorValues data.cusp (HomogeneousPoly degree) :=
  let primitive := goodLineCuspidalPrismRectangle data trivial basis source cocycle parameter
    left₁ right₁ left₂ right₂ ordered₁ ordered₂
  let unipotent := GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)
  primitive (fun position => unipotent * vertices position) -
    cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi unipotent) (primitive vertices)

theorem goodLineCuspidalPrismRectangleDefect_integral {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (left₁ right₁ left₂ right₂ : ℝ)
    (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂)
    (radical : RadicalLattice) (vertices : Fin 2 → RealGL3) :
    let values (real : ℝ × ℝ) := cuspidalTensorHilbertEmbedding data.cusp basis
      (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) 1 vertices)
    cuspidalTensorHilbertEmbedding data.cusp basis
        (goodLineCuspidalPrismRectangleDefect data trivial basis source cocycle parameter
          left₁ right₁ left₂ right₂ ordered₁ ordered₂ radical vertices) =
      basisHilbertCoefficient data.cusp basis
        (realCoefficientComponent degree data.chi
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)))
        (∫ real in Set.Icc left₁ right₁ ×ˢ Set.Icc left₂ right₂,
          standardGoodLineRealKernel parameter real •
            (values (goodLineRadicalRealShift radical real) - values real)
          ∂((volume : Measure ℝ).prod volume)) := by
  let : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly degree)).addCommGroup
  let domain := Set.Icc left₁ right₁ ×ˢ Set.Icc left₂ right₂
  have original := goodLineCuspidalVertexPrism_integrableOn_compact data trivial basis source cocycle
    1 vertices parameter domain (isCompact_Icc.prod isCompact_Icc)
  have shifted := goodLineCuspidalVertexPrism_radicalShift_integrableOn_compact data trivial basis source cocycle
    1 vertices parameter radical domain (isCompact_Icc.prod isCompact_Icc)
  let operator := basisHilbertCoefficient data.cusp basis
    (realCoefficientComponent degree data.chi
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)))
  have commute := operator.integral_comp_comm shifted
  simp only [map_smul] at commute
  dsimp only
  simp only [goodLineCuspidalPrismRectangleDefect, map_sub, cuspidalTensorHilbertEmbedding_map,
    goodLineCuspidalPrismRectangle_embedding, goodLineCuspidalPrismTruncatedIntegral,
    goodLineCuspidalVertexPrism_radical_translate, smul_sub]
  rw [integral_sub shifted original, map_sub]
  change (∫ real in domain, standardGoodLineRealKernel parameter real •
      operator (cuspidalTensorHilbertEmbedding data.cusp basis
        (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
          (standardGoodLineRealArgument (goodLineRadicalRealShift radical real)) 1 vertices))
        ∂((volume : Measure ℝ).prod volume)) - _ = _
  rw [commute]

theorem goodLineCuspidalPrismRectangleDefect_boundary {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (left₁ right₁ left₂ right₂ : ℝ)
    (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂)
    (radical : RadicalLattice) (vertices : Fin 2 → RealGL3) :
    let domain := Set.Icc left₁ right₁ ×ˢ Set.Icc left₂ right₂
    let values (real : ℝ × ℝ) := cuspidalTensorHilbertEmbedding data.cusp basis
      (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) 1 vertices)
    cuspidalTensorHilbertEmbedding data.cusp basis
        (goodLineCuspidalPrismRectangleDefect data trivial basis source cocycle parameter
          left₁ right₁ left₂ right₂ ordered₁ ordered₂ radical vertices) =
      basisHilbertCoefficient data.cusp basis
        (realCoefficientComponent degree data.chi
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)))
        ((∫ real in (goodLineRadicalRealShift radical '' domain) \ domain,
            standardGoodLineRealKernel parameter (goodLineRadicalRealShift radical⁻¹ real) • values real
            ∂((volume : Measure ℝ).prod volume)) -
          (∫ real in domain \ (goodLineRadicalRealShift radical '' domain),
            standardGoodLineRealKernel parameter real • values real ∂((volume : Measure ℝ).prod volume)) +
          ∫ real in (goodLineRadicalRealShift radical '' domain) ∩ domain,
            (standardGoodLineRealKernel parameter (goodLineRadicalRealShift radical⁻¹ real) -
              standardGoodLineRealKernel parameter real) • values real ∂((volume : Measure ℝ).prod volume)) := by
  dsimp only
  rw [goodLineCuspidalPrismRectangleDefect_integral]
  congr 1
  exact setIntegral_goodLineKernel_difference _
    (goodLineCuspidalVertexPrism_hilbertContDiff data trivial basis source cocycle 1 vertices).continuous
    parameter radical _ (isCompact_Icc.prod isCompact_Icc)

theorem goodLineCuspidalPrismRectangleDefect_endpoint {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (left₁ right₁ left₂ right₂ : ℝ) (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂)
    (radical : RadicalLattice) (vertices : Fin 2 → RealGL3) :
    let domain := Set.Icc left₁ right₁ ×ˢ Set.Icc left₂ right₂
    let values (real : ℝ × ℝ) := cuspidalTensorHilbertEmbedding data.cusp basis
      (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) 1 vertices)
    cuspidalTensorHilbertEmbedding data.cusp basis
        (goodLineCuspidalPrismRectangleDefect data trivial basis source cocycle cohomologicalPoint
          left₁ right₁ left₂ right₂ ordered₁ ordered₂ radical vertices) =
      basisHilbertCoefficient data.cusp basis
        (realCoefficientComponent degree data.chi
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)))
        ((∫ real in (goodLineRadicalRealShift radical '' domain) \ domain,
            values real ∂((volume : Measure ℝ).prod volume)) -
          ∫ real in domain \ (goodLineRadicalRealShift radical '' domain),
            values real ∂((volume : Measure ℝ).prod volume)) := by
  simpa only [standardGoodLineRealKernel_endpoint, one_smul, sub_self, zero_smul, integral_zero, add_zero] using
    goodLineCuspidalPrismRectangleDefect_boundary data trivial basis source cocycle cohomologicalPoint
      left₁ right₁ left₂ right₂ ordered₁ ordered₂ radical vertices

end TernaryPeriodPolynomials.SphericalDetection.Helpers
