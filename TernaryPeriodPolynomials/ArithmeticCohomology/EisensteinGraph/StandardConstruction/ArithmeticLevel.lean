module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FiniteApproximation
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TopologicalMatrices
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Comparison

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ArithmeticLevel

theorem rationalMatrix_integral (matrix : Matrix (Fin 3) (Fin 3) ℚ)
    (integral : ∀ row column, algebraMap ℚ FiniteAdeles (matrix row column) ∈
      Set.range integralEmbedding) :
    ∃ integerMatrix : Matrix (Fin 3) (Fin 3) ℤ,
      integerMatrix.map (Int.castRingHom ℚ) = matrix := by
  have entries : ∀ row column, ∃ integer : ℤ, (integer : ℚ) = matrix row column := by
    intro row column
    obtain ⟨integer, equality⟩ :=
      (FiniteApproximation.rational_integral_iff (matrix row column)).mp (integral row column)
    exact ⟨integer, equality.symm⟩
  choose integer equality using entries
  exact ⟨integer, funext (fun row => funext (fun column => equality row column))⟩

theorem rationalGL_integral (element : RationalGL3)
    (integral : rationalFinite element ∈
      Set.range (GeneralLinearGroup.map integralEmbedding)) :
    ∃ integerElement : IntegralGL3,
      GeneralLinearGroup.map (Int.castRingHom ℚ) integerElement = element := by
  obtain ⟨integralElement, integralEquality⟩ := integral
  have valueIntegral : ∀ row column, algebraMap ℚ FiniteAdeles (element.val row column) ∈
      Set.range integralEmbedding := by
    intro row column
    exact ⟨integralElement.val row column,
      congrArg (fun matrix => matrix.val row column) integralEquality⟩
  have inverseIntegral : ∀ row column, algebraMap ℚ FiniteAdeles (element.inv row column) ∈
      Set.range integralEmbedding := by
    intro row column
    exact ⟨integralElement.inv row column,
      congrArg (fun matrix => matrix.inv row column) integralEquality⟩
  obtain ⟨value, valueEquality⟩ := rationalMatrix_integral element.val valueIntegral
  obtain ⟨inverse, inverseEquality⟩ := rationalMatrix_integral element.inv inverseIntegral
  have leftInverse : value * inverse = 1 := by
    apply Matrix.map_injective (Int.cast_injective (α := ℚ))
    change (value * inverse).map (Int.castRingHom ℚ) = (1 : Matrix (Fin 3) (Fin 3) ℤ).map _
    rw [Matrix.map_mul, valueEquality, inverseEquality, element.val_inv]
    simp
  have rightInverse : inverse * value = 1 := by
    apply Matrix.map_injective (Int.cast_injective (α := ℚ))
    change (inverse * value).map (Int.castRingHom ℚ) = (1 : Matrix (Fin 3) (Fin 3) ℤ).map _
    rw [Matrix.map_mul, valueEquality, inverseEquality, element.inv_val]
    simp
  refine ⟨⟨value, inverse, leftInverse, rightInverse⟩, ?_⟩
  exact Units.ext valueEquality

theorem rationalLevel_of_finiteLevel (element : RationalGL3)
    (membership : rationalFinite element ∈ finiteLevel) : element ∈ rationalLevel := by
  obtain ⟨integralElement, integralMembership, integralEquality⟩ := Subgroup.mem_map.mp membership
  obtain ⟨integerElement, integerEquality⟩ :=
    rationalGL_integral element ⟨integralElement, integralEquality⟩
  have finiteEquality : integralFinite integerElement = rationalFinite element :=
    congrArg rationalFinite integerEquality
  rw [Comparison.integralFinite_integralMap] at finiteEquality
  have integralLiftEquality : GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integerElement =
      integralElement :=
    TopologicalMatrices.integralGL_isOpenEmbedding.injective
      (finiteEquality.trans integralEquality.symm)
  have reductionEquality : GeneralLinearGroup.map integralReduction
      (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integerElement) =
        reductionThree integerElement := by
    apply GeneralLinearGroup.ext
    intro row column
    change integralReduction ((integerElement.val row column : ℤ) : IntegralAdeles) =
      ((integerElement.val row column : ℤ) : ZMod 3)
    simp
  have arithmeticMembership : integerElement ∈ arithmeticLevel := by
    change reductionThree integerElement ∈ rowStabilizer
    rw [← reductionEquality, integralLiftEquality]
    exact integralMembership
  exact ⟨⟨integerElement, arithmeticMembership⟩, integerEquality⟩

theorem rationalLevel_iff_finiteLevel (element : RationalGL3) :
    element ∈ rationalLevel ↔ rationalFinite element ∈ finiteLevel :=
  ⟨fun membership => Comparison.rationalLevel_finiteLevel ⟨element, membership⟩,
    rationalLevel_of_finiteLevel element⟩

theorem finite_representatives_disjoint (correspondence : HeckeCorrespondence)
    (first : RationalGL3) (firstMembership : first ∈ correspondence.representatives)
    (second : RationalGL3) (secondMembership : second ∈ correspondence.representatives)
    (related : (rationalFinite first)⁻¹ * rationalFinite second ∈ finiteLevel) : first = second := by
  apply correspondence.disjoint first firstMembership second secondMembership
  apply rationalLevel_of_finiteLevel
  simpa only [map_mul, map_inv] using related

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ArithmeticLevel
