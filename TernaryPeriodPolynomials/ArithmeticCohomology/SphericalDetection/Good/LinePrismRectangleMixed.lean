module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismRectangle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorIntegralMap

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineCuspidalMixedPrimitiveValue_integral {degree : ℕ} {index X : Type}
    [Fintype index] [MeasurableSpace X]
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (measure : Measure X) (weight : X → ℂ)
    (primitives : X → (Fin 2 → RealGL3) → cuspidalTensorValues cusp (HomogeneousPoly degree))
    (result : (Fin 2 → RealGL3) → cuspidalTensorValues cusp (HomogeneousPoly degree))
    (integrable : ∀ vertices, Integrable (fun point => weight point •
      cuspidalTensorHilbertEmbedding cusp basis (primitives point vertices)) measure)
    (equality : ∀ vertices, cuspidalTensorHilbertEmbedding cusp basis (result vertices) =
      ∫ point, weight point • cuspidalTensorHilbertEmbedding cusp basis (primitives point vertices) ∂measure)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    Integrable (fun point => weight point • cuspidalTensorHilbertEmbedding cusp basis
      (goodLineCuspidalMixedPrimitiveValue cusp (primitives point) matrix radical)) measure ∧
    cuspidalTensorHilbertEmbedding cusp basis (goodLineCuspidalMixedPrimitiveValue cusp result matrix radical) =
      ∫ point, weight point • cuspidalTensorHilbertEmbedding cusp basis
        (goodLineCuspidalMixedPrimitiveValue cusp (primitives point) matrix radical) ∂measure := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  let levi := GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)
  let unipotent := GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)
  have first := integrable ![levi, unipotent * levi]
  have second := integrable ![unipotent, unipotent * levi]
  have third := integrable ![1, levi]
  have fourth := integrable ![1, unipotent]
  constructor
  · simp only [goodLineCuspidalMixedPrimitiveValue, map_sub, map_add, smul_sub, smul_add]
    exact ((first.sub second).add third).sub fourth
  · simp only [goodLineCuspidalMixedPrimitiveValue, map_sub, map_add, equality, smul_sub, smul_add]
    change _ = ∫ point, (weight point • cuspidalTensorHilbertEmbedding cusp basis
        (primitives point ![levi, unipotent * levi]) -
      weight point • cuspidalTensorHilbertEmbedding cusp basis (primitives point ![unipotent, unipotent * levi]) +
      weight point • cuspidalTensorHilbertEmbedding cusp basis (primitives point ![1, levi])) -
      weight point • cuspidalTensorHilbertEmbedding cusp basis (primitives point ![1, unipotent]) ∂measure
    have difference : Integrable (fun point => weight point • cuspidalTensorHilbertEmbedding cusp basis
        (primitives point ![levi, unipotent * levi]) -
      weight point • cuspidalTensorHilbertEmbedding cusp basis (primitives point ![unipotent, unipotent * levi]))
        measure := first.sub second
    have addition : Integrable (fun point => weight point • cuspidalTensorHilbertEmbedding cusp basis
        (primitives point ![levi, unipotent * levi]) -
      weight point • cuspidalTensorHilbertEmbedding cusp basis (primitives point ![unipotent, unipotent * levi]) +
      weight point • cuspidalTensorHilbertEmbedding cusp basis (primitives point ![1, levi])) measure :=
      difference.add third
    rw [integral_sub addition fourth, integral_add difference third, integral_sub first second]

def goodLineMixedCuspidalRectangle {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (left₁ right₁ left₂ right₂ : ℝ)
    (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    cuspidalTensorValues data.cusp (Binary.HomogeneousPoly (degree + 1)) :=
  let primitive := goodLineCuspidalPrismRectangle data trivial basis source cocycle parameter
    left₁ right₁ left₂ right₂ ordered₁ ordered₂
  cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 0)
      (goodLineCuspidalMixedPrimitiveValue data.cusp primitive matrix radicalLatticeFirst) +
    cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 1)
      (goodLineCuspidalMixedPrimitiveValue data.cusp primitive matrix radicalLatticeSecond)

theorem goodLineMixedCuspidalRectangle_integral {degree : ℕ} {index targetIndex : Type}
    [Fintype index] [Fintype targetIndex]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (targetBasis : Module.Basis targetIndex ℂ (Binary.HomogeneousPoly (degree + 1)))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (parameter : ℂ) (left₁ right₁ left₂ right₂ : ℝ)
    (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    IntegrableOn (fun real => standardGoodLineRealKernel parameter real •
      cuspidalTensorHilbertEmbedding data.cusp targetBasis
        (goodLineMixedCuspidalValues data source cocycle matrix (atInfinity (standardGoodLineRealArgument real))))
      (Set.Icc left₁ right₁ ×ˢ Set.Icc left₂ right₂) ((volume : Measure ℝ).prod volume) ∧
    cuspidalTensorHilbertEmbedding data.cusp targetBasis
        (goodLineMixedCuspidalRectangle data trivial basis source cocycle parameter
          left₁ right₁ left₂ right₂ ordered₁ ordered₂ matrix) =
      ∫ real in Set.Icc left₁ right₁ ×ˢ Set.Icc left₂ right₂,
        standardGoodLineRealKernel parameter real • cuspidalTensorHilbertEmbedding data.cusp targetBasis
          (goodLineMixedCuspidalValues data source cocycle matrix (atInfinity (standardGoodLineRealArgument real)))
            ∂((volume : Measure ℝ).prod volume) := by
  let primitive (real : ℝ × ℝ) := sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
    (standardGoodLineRealArgument real) 1
  let integrated := goodLineCuspidalPrismRectangle data trivial basis source cocycle parameter
    left₁ right₁ left₂ right₂ ordered₁ ordered₂
  let domain := Set.Icc left₁ right₁ ×ˢ Set.Icc left₂ right₂
  let measure := ((volume : Measure ℝ).prod volume).restrict domain
  have primitive_integrable (vertices : Fin 2 → RealGL3) :
      Integrable (fun real => standardGoodLineRealKernel parameter real •
        cuspidalTensorHilbertEmbedding data.cusp basis (primitive real vertices)) measure :=
    goodLineCuspidalVertexPrism_integrableOn_compact data trivial basis source cocycle
      1 vertices parameter domain (isCompact_Icc.prod isCompact_Icc)
  have primitive_equality (vertices : Fin 2 → RealGL3) :
      cuspidalTensorHilbertEmbedding data.cusp basis (integrated vertices) =
        ∫ real, standardGoodLineRealKernel parameter real •
          cuspidalTensorHilbertEmbedding data.cusp basis (primitive real vertices) ∂measure :=
    goodLineCuspidalPrismRectangle_embedding data trivial basis source cocycle parameter
      left₁ right₁ left₂ right₂ ordered₁ ordered₂ vertices
  have mixed_formula (radical : RadicalLattice) := goodLineCuspidalMixedPrimitiveValue_integral
    data.cusp basis measure (standardGoodLineRealKernel parameter) primitive integrated
      primitive_integrable primitive_equality matrix radical
  have component (position : Fin 2) (radical : RadicalLattice) :
      Integrable (fun real => standardGoodLineRealKernel parameter real •
        cuspidalTensorHilbertEmbedding data.cusp targetBasis
          (cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree position)
            (goodLineCuspidalMixedPrimitiveValue data.cusp (primitive real) matrix radical))) measure ∧
      cuspidalTensorHilbertEmbedding data.cusp targetBasis
          (cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree position)
            (goodLineCuspidalMixedPrimitiveValue data.cusp integrated matrix radical)) =
        ∫ real, standardGoodLineRealKernel parameter real •
          cuspidalTensorHilbertEmbedding data.cusp targetBasis
            (cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree position)
              (goodLineCuspidalMixedPrimitiveValue data.cusp (primitive real) matrix radical)) ∂measure := by
    constructor
    · have mapped := (cuspidalTensorHilbertMap data.cusp basis targetBasis
        (lowerRadicalLatticeContribution degree position)).integrable_comp (mixed_formula radical).1
      simpa only [map_smul, cuspidalTensorHilbertMap_embedding] using mapped
    · have integrable : Integrable (fun real => cuspidalTensorHilbertEmbedding data.cusp basis
          (standardGoodLineRealKernel parameter real •
            goodLineCuspidalMixedPrimitiveValue data.cusp (primitive real) matrix radical)) measure := by
        simpa only [map_smul] using (mixed_formula radical).1
      have equality : cuspidalTensorHilbertEmbedding data.cusp basis
          (goodLineCuspidalMixedPrimitiveValue data.cusp integrated matrix radical) =
        ∫ real, cuspidalTensorHilbertEmbedding data.cusp basis
          (standardGoodLineRealKernel parameter real •
            goodLineCuspidalMixedPrimitiveValue data.cusp (primitive real) matrix radical) ∂measure := by
        simpa only [map_smul] using (mixed_formula radical).2
      simpa only [map_smul] using cuspidalTensorMap_integral data.cusp basis targetBasis
        (lowerRadicalLatticeContribution degree position) measure _ integrable _ equality
  obtain ⟨first_integrable, first_equality⟩ := component 0 radicalLatticeFirst
  obtain ⟨second_integrable, second_equality⟩ := component 1 radicalLatticeSecond
  constructor
  · simp only [goodLineMixedCuspidalValues_prism data source cocycle diagonal, map_add, smul_add]
    exact first_integrable.add second_integrable
  · simp only [goodLineMixedCuspidalRectangle, goodLineMixedCuspidalValues_prism data source cocycle diagonal,
      map_add, smul_add]
    change _ + _ = ∫ real, standardGoodLineRealKernel parameter real •
      cuspidalTensorHilbertEmbedding data.cusp targetBasis
        (cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 0)
          (goodLineCuspidalMixedPrimitiveValue data.cusp (primitive real) matrix radicalLatticeFirst)) +
      standardGoodLineRealKernel parameter real • cuspidalTensorHilbertEmbedding data.cusp targetBasis
        (cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 1)
          (goodLineCuspidalMixedPrimitiveValue data.cusp (primitive real) matrix radicalLatticeSecond)) ∂measure
    rw [integral_add first_integrable second_integrable]
    exact congrArg₂ (· + ·) first_equality second_equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
