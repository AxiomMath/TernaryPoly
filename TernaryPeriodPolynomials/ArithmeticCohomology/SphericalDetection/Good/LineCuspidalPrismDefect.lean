module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismRectangleDefect

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineCuspidalRadicalPrimitiveValue {degree : ℕ} (cusp : CuspidalRepresentation)
    (primitive : (Fin 2 → RealGL3) → cuspidalTensorValues cusp (HomogeneousPoly degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    cuspidalTensorValues cusp (HomogeneousPoly degree) :=
  let levi := GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)
  let unipotent := GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)
  primitive ![levi, unipotent * levi] - primitive ![1, unipotent]

def goodLineCuspidalShiftPrimitiveValue {degree : ℕ} (cusp : CuspidalRepresentation)
    (character : RankOneCharacter)
    (primitive : (Fin 2 → RealGL3) → cuspidalTensorValues cusp (HomogeneousPoly degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    cuspidalTensorValues cusp (HomogeneousPoly degree) :=
  let levi := GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)
  let unipotent := GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)
  primitive ![unipotent, unipotent * levi] -
    cuspidalTensorMap cusp (realCoefficientComponent degree character unipotent) (primitive ![1, levi])

theorem goodLineCuspidalMixedPrimitiveValue_defect {degree : ℕ} (positive : 0 < degree)
    (cusp : CuspidalRepresentation)
    (primitive : (Fin 2 → RealGL3) → cuspidalTensorValues cusp (HomogeneousPoly degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    (cuspidalTensorMap cusp (lowerRadicalLatticeContribution degree 0)
        (goodLineCuspidalMixedPrimitiveValue cusp primitive matrix radicalLatticeFirst) +
      cuspidalTensorMap cusp (lowerRadicalLatticeContribution degree 1)
        (goodLineCuspidalMixedPrimitiveValue cusp primitive matrix radicalLatticeSecond)) =
    (cuspidalTensorMap cusp (lowerRadicalLatticeContribution degree 0)
        (goodLineCuspidalRadicalPrimitiveValue cusp primitive matrix radicalLatticeFirst) +
      cuspidalTensorMap cusp (lowerRadicalLatticeContribution degree 1)
        (goodLineCuspidalRadicalPrimitiveValue cusp primitive matrix radicalLatticeSecond)) -
    (cuspidalTensorMap cusp (lowerRadicalLatticeContribution degree 0)
        (goodLineCuspidalShiftPrimitiveValue cusp trivialCharacter primitive matrix radicalLatticeFirst) +
      cuspidalTensorMap cusp (lowerRadicalLatticeContribution degree 1)
        (goodLineCuspidalShiftPrimitiveValue cusp trivialCharacter primitive matrix radicalLatticeSecond)) := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  let : AddCommGroup (cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1))) :=
    (cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1))).addCommGroup
  let levi := GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)
  let boundary (radical : RadicalLattice) :=
    cuspidalTensorMap cusp (realCoefficientComponent degree trivialCharacter
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)))
      (primitive ![1, levi]) - primitive ![1, levi]
  have term (radical : RadicalLattice) :
      goodLineCuspidalMixedPrimitiveValue cusp primitive matrix radical =
        goodLineCuspidalRadicalPrimitiveValue cusp primitive matrix radical -
          goodLineCuspidalShiftPrimitiveValue cusp trivialCharacter primitive matrix radical - boundary radical := by
    dsimp only [goodLineCuspidalMixedPrimitiveValue, goodLineCuspidalRadicalPrimitiveValue,
      goodLineCuspidalShiftPrimitiveValue, boundary, levi]
    abel
  have boundary_zero : cuspidalTensorMap cusp (lowerRadicalLatticeContribution degree 0) (boundary radicalLatticeFirst) +
      cuspidalTensorMap cusp (lowerRadicalLatticeContribution degree 1) (boundary radicalLatticeSecond) = 0 := by
    apply Subtype.ext
    funext argument
    exact lowerRadicalLatticeContribution_boundary degree positive ((primitive ![1, levi]).val argument)
  rw [term, term]
  simp only [map_sub]
  linear_combination (norm := abel) -boundary_zero

theorem goodLineCuspidalPrismRectangle_shift {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (left₁ right₁ left₂ right₂ : ℝ)
    (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    goodLineCuspidalShiftPrimitiveValue data.cusp data.chi
        (goodLineCuspidalPrismRectangle data trivial basis source cocycle parameter
          left₁ right₁ left₂ right₂ ordered₁ ordered₂) matrix radical =
      goodLineCuspidalPrismRectangleDefect data trivial basis source cocycle parameter
        left₁ right₁ left₂ right₂ ordered₁ ordered₂ radical
        ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)] := by
  have vertices : (fun position : Fin 2 =>
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical) *
        ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)] position) =
      ![GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical),
        GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical) *
          GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)] := by
    funext position
    fin_cases position <;> simp
  simp only [goodLineCuspidalShiftPrimitiveValue, goodLineCuspidalPrismRectangleDefect, vertices]

theorem goodLineMixedCuspidalRectangle_defect {degree : ℕ} {index : Type} [Fintype index]
    (positive : 0 < degree) (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (left₁ right₁ left₂ right₂ : ℝ)
    (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    let primitive := goodLineCuspidalPrismRectangle data trivial basis source cocycle parameter
      left₁ right₁ left₂ right₂ ordered₁ ordered₂
    let vertices := ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)]
    goodLineMixedCuspidalRectangle data trivial basis source cocycle parameter
        left₁ right₁ left₂ right₂ ordered₁ ordered₂ matrix =
    (cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 0)
        (goodLineCuspidalRadicalPrimitiveValue data.cusp primitive matrix radicalLatticeFirst) +
      cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 1)
        (goodLineCuspidalRadicalPrimitiveValue data.cusp primitive matrix radicalLatticeSecond)) -
    (cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 0)
        (goodLineCuspidalPrismRectangleDefect data trivial basis source cocycle parameter
          left₁ right₁ left₂ right₂ ordered₁ ordered₂ radicalLatticeFirst vertices) +
      cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 1)
        (goodLineCuspidalPrismRectangleDefect data trivial basis source cocycle parameter
          left₁ right₁ left₂ right₂ ordered₁ ordered₂ radicalLatticeSecond vertices)) := by
  dsimp only
  rw [goodLineMixedCuspidalRectangle, goodLineCuspidalMixedPrimitiveValue_defect positive]
  rw [← trivial, goodLineCuspidalPrismRectangle_shift, goodLineCuspidalPrismRectangle_shift]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
