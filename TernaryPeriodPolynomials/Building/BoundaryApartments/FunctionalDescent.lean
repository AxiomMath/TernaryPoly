module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.Surjectivity

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

theorem normalizedFrame_arithmetic_mul (matrix : arithmeticLevel) (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    ∀ column, ((matrix.val * frame).val 2 column : ZMod 3) = 1 := by
  intro column
  have last := arithmetic_mulVec_last matrix (fun row => frame.val row column)
  change ((matrix.val.val * frame.val) 2 column : ZMod 3) = 1
  exact last.trans (normalized column)

theorem polynomialFunctional_of_normalization {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (normalization : ∀ frame : IntegralGL3,
      (∀ column, (frame.val 2 column : ZMod 3) = 1) →
      functional (apartment (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) =
        framePolynomial degree frame polynomial) :
    IsPolynomialFunctional polynomial functional := by
  have orbit_value (matrix : rationalLevel) :
      functional (translateGoodCycle matrix referenceApartment).val =
        rationalCoefficientComponent degree trivialCharacter matrix.val
          (framePolynomial degree referenceFrame polynomial) := by
    obtain ⟨integral, integral_eq⟩ := matrix.property
    change functional (translateChain matrix.val
      (apartment (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame))) = _
    rw [apartment_translate, ← integral_eq]
    change functional (apartment (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) integral.val *
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame)) = _
    rw [← map_mul, normalization (integral.val * referenceFrame)
      (normalizedFrame_arithmetic_mul integral referenceFrame referenceFrame_normalized)]
    simp only [framePolynomial, map_mul, Module.End.mul_apply]
    rfl
  have maps : functional.comp (goodCycleModule.subtype.comp apartmentPresentationMap) =
      apartmentSymbolValue polynomial := by
    apply Finsupp.lhom_ext
    intro matrix scalar
    simp only [LinearMap.comp_apply, apartmentPresentationMap, apartmentSymbolValue,
      Finsupp.linearCombination_single, Submodule.subtype_apply, map_smul, orbit_value]
  have cycle_value (symbols : ApartmentSymbols) :
      functional (apartmentPresentationMap symbols).val = apartmentSymbolValue polynomial symbols :=
    LinearMap.congr_fun maps symbols
  constructor
  · intro matrix chain cycle
    obtain ⟨symbols, value⟩ := apartmentPresentationMap_surjective ⟨chain, cycle⟩
    have chain_eq : (apartmentPresentationMap symbols).val = chain := congrArg Subtype.val value
    rw [← chain_eq, cycle_value]
    change functional (translateGoodCycle matrix (apartmentPresentationMap symbols)).val = _
    rw [← apartmentPresentationMap_translate, cycle_value, apartmentSymbolValue_translate]
  · intro frame normalized
    rw [normalization frame normalized]
    exact rationalCoefficient_integralFrame degree frame polynomial

theorem polynomialFunctional_apartmentValue {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (property : IsPolynomialFunctional polynomial functional) (symbols : ApartmentSymbols) :
    functional (apartmentPresentationMap symbols).val = apartmentSymbolValue polynomial symbols := by
  have reference_value : functional referenceApartment.val = framePolynomial degree referenceFrame polynomial := by
    apply Subtype.ext
    exact (property.2 referenceFrame referenceFrame_normalized).trans
      (rationalCoefficient_integralFrame degree referenceFrame polynomial).symm
  have maps : functional.comp (goodCycleModule.subtype.comp apartmentPresentationMap) =
      apartmentSymbolValue polynomial := by
    apply Finsupp.lhom_ext
    intro matrix scalar
    simp only [LinearMap.comp_apply, apartmentPresentationMap, apartmentSymbolValue,
      Finsupp.linearCombination_single, Submodule.subtype_apply, map_smul]
    change scalar • functional (translateChain matrix.val referenceApartment.val) = _
    rw [property.1 matrix referenceApartment.val referenceApartment.property, reference_value]
  exact LinearMap.congr_fun maps symbols

theorem polynomialFunctional_kernel_inclusion {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (property : IsPolynomialFunctional polynomial functional) :
    apartmentPresentationMap.ker ≤ (apartmentSymbolValue polynomial).ker := by
  intro symbols zero_symbols
  change apartmentSymbolValue polynomial symbols = 0
  rw [← polynomialFunctional_apartmentValue property symbols]
  have zero_value : apartmentPresentationMap symbols = 0 := zero_symbols
  rw [zero_value, Submodule.coe_zero, map_zero]

theorem polynomialFunctional_exists_of_valueKernel {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (kernel : apartmentPresentationMap.ker ≤ (apartmentSymbolValue polynomial).ker) :
    ∃ functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree,
      IsPolynomialFunctional polynomial functional := by
  let quotient_equiv : (ApartmentSymbols ⧸ apartmentPresentationMap.ker) ≃ₗ[ℂ] goodCycleModule :=
    @LinearMap.quotKerEquivOfSurjective ℂ ApartmentSymbols goodCycleModule
      inferInstance inferInstance (Submodule.addCommGroup goodCycleModule)
      inferInstance (Submodule.module goodCycleModule) apartmentPresentationMap
      apartmentPresentationMap_surjective
  let value_map := apartmentPresentationMap.ker.liftQ (apartmentSymbolValue polynomial) kernel
  let cycle_map : goodCycleModule →ₗ[ℂ] HomogeneousPoly degree :=
    value_map.comp quotient_equiv.symm.toLinearMap
  have cycle_value (symbols : ApartmentSymbols) :
      cycle_map (apartmentPresentationMap symbols) = apartmentSymbolValue polynomial symbols := by
    have forward : quotient_equiv (Submodule.Quotient.mk symbols) =
        apartmentPresentationMap symbols := rfl
    change value_map (quotient_equiv.symm (apartmentPresentationMap symbols)) = _
    rw [← forward, LinearEquiv.symm_apply_apply]
    rfl
  apply polynomialFunctional_exists_of_referenceCycleMap polynomial cycle_map
  · intro matrix chain
    obtain ⟨symbols, rfl⟩ := apartmentPresentationMap_surjective chain
    rw [← apartmentPresentationMap_translate, cycle_value, cycle_value,
      apartmentSymbolValue_translate]
  · have reference : apartmentPresentationMap (Finsupp.single 1 1) = referenceApartment := by
      simp only [apartmentPresentationMap, Finsupp.linearCombination_single, one_smul,
        translateGoodCycle_one]
    change cycle_map referenceApartment = _
    rw [← reference, cycle_value]
    simp only [apartmentSymbolValue, Finsupp.linearCombination_single, one_smul,
      Subgroup.coe_one, map_one, Module.End.one_apply]

theorem polynomialFunctional_exists_iff_valueKernel {degree : ℕ} (polynomial : HomogeneousPoly degree) :
    (∃ functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree,
      IsPolynomialFunctional polynomial functional) ↔
        apartmentPresentationMap.ker ≤ (apartmentSymbolValue polynomial).ker := by
  constructor
  · rintro ⟨functional, property⟩
    exact polynomialFunctional_kernel_inclusion property
  · exact polynomialFunctional_exists_of_valueKernel polynomial

theorem polynomialFunctional_unique_on_goodCycles {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {first second : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (first_property : IsPolynomialFunctional polynomial first)
    (second_property : IsPolynomialFunctional polynomial second)
    {chain : EdgeChains} (cycle : GoodCycle chain) : first chain = second chain := by
  obtain ⟨symbols, value⟩ := apartmentPresentationMap_surjective ⟨chain, cycle⟩
  have chain_eq : (apartmentPresentationMap symbols).val = chain := congrArg Subtype.val value
  rw [← chain_eq, polynomialFunctional_apartmentValue first_property,
    polynomialFunctional_apartmentValue second_property]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
