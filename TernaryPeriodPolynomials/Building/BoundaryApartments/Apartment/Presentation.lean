module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.ChainRelations

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

abbrev ApartmentSymbols := rationalLevel →₀ ℂ

def apartmentPresentationMap : ApartmentSymbols →ₗ[ℂ] goodCycleModule :=
  Finsupp.linearCombination ℂ (fun matrix => translateGoodCycle matrix referenceApartment)

def apartmentSymbolTranslate (matrix : rationalLevel) : ApartmentSymbols →ₗ[ℂ] ApartmentSymbols :=
  Finsupp.lmapDomain ℂ ℂ (fun index => matrix * index)

def apartmentSymbolValue {degree : ℕ} (polynomial : HomogeneousPoly degree) :
    ApartmentSymbols →ₗ[ℂ] HomogeneousPoly degree :=
  Finsupp.linearCombination ℂ (fun matrix =>
    rationalCoefficientComponent degree trivialCharacter matrix.val
      (framePolynomial degree referenceFrame polynomial))

def apartmentRelation (index : rationalLevel × Fin 3) : ApartmentSymbols :=
  match index.2 with
  | 0 => Finsupp.single index.1 1 + Finsupp.single (index.1 * apartmentNormGenerator) 1 +
      Finsupp.single (index.1 * apartmentNormGenerator ^ 2) 1
  | 1 => Finsupp.single (index.1 * apartmentCyclicGenerator) 1 - Finsupp.single index.1 1
  | 2 => Finsupp.single (index.1 * apartmentSwapGenerator) 1 + Finsupp.single index.1 1

def apartmentRelations : Submodule ℂ ApartmentSymbols :=
  Submodule.span ℂ (Set.range apartmentRelation)

theorem apartmentPresentationMap_translate (matrix : rationalLevel) (symbols : ApartmentSymbols) :
    apartmentPresentationMap (apartmentSymbolTranslate matrix symbols) =
      translateGoodCycle matrix (apartmentPresentationMap symbols) := by
  have maps : apartmentPresentationMap.comp (apartmentSymbolTranslate matrix) =
      (translateGoodCycle matrix).comp apartmentPresentationMap := by
    apply Finsupp.lhom_ext
    intro index scalar
    simp only [LinearMap.comp_apply, apartmentSymbolTranslate, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, apartmentPresentationMap, Finsupp.linearCombination_single,
      map_smul, translateGoodCycle_mul]
  exact LinearMap.congr_fun maps symbols

theorem apartmentSymbolValue_translate {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (matrix : rationalLevel) (symbols : ApartmentSymbols) :
    apartmentSymbolValue polynomial (apartmentSymbolTranslate matrix symbols) =
      rationalCoefficientComponent degree trivialCharacter matrix.val
        (apartmentSymbolValue polynomial symbols) := by
  have maps : (apartmentSymbolValue polynomial).comp (apartmentSymbolTranslate matrix) =
      (rationalCoefficientComponent degree trivialCharacter matrix.val).comp
        (apartmentSymbolValue polynomial) := by
    apply Finsupp.lhom_ext
    intro index scalar
    simp only [LinearMap.comp_apply, apartmentSymbolTranslate, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, apartmentSymbolValue, Finsupp.linearCombination_single,
      map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  exact LinearMap.congr_fun maps symbols

theorem apartmentRelations_le_kernel : apartmentRelations ≤ apartmentPresentationMap.ker := by
  apply Submodule.span_le.mpr
  rintro symbols ⟨⟨matrix, index⟩, rfl⟩
  change apartmentPresentationMap (apartmentRelation (matrix, index)) = 0
  fin_cases index
  · simp only [apartmentRelation, apartmentPresentationMap, map_add,
      Finsupp.linearCombination_single, one_smul, translateGoodCycle_mul]
    rw [← map_add, ← map_add, referenceApartment_norm_relation, map_zero]
  · simp only [apartmentRelation, apartmentPresentationMap, map_sub,
      Finsupp.linearCombination_single, one_smul, translateGoodCycle_mul,
      referenceApartment_cyclic_relation, sub_self]
  · simp only [apartmentRelation, apartmentPresentationMap, map_add,
      Finsupp.linearCombination_single, one_smul, translateGoodCycle_mul,
      referenceApartment_swap_relation]
    apply Subtype.ext
    change translateChain matrix.val (-referenceApartment.val) +
      translateChain matrix.val referenceApartment.val = 0
    rw [map_neg, neg_add_cancel]

theorem apartmentRelations_le_valueKernel {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) :
    apartmentRelations ≤ (apartmentSymbolValue polynomial).ker := by
  apply Submodule.span_le.mpr
  rintro symbols ⟨⟨matrix, index⟩, rfl⟩
  change apartmentSymbolValue polynomial (apartmentRelation (matrix, index)) = 0
  fin_cases index
  · simp only [apartmentRelation, apartmentSymbolValue, map_add,
      Finsupp.linearCombination_single, one_smul, Subgroup.coe_mul, map_mul,
      Module.End.mul_apply]
    rw [← map_add, ← map_add, apartmentNormGenerator_norm solution, map_zero]
  · simp only [apartmentRelation, apartmentSymbolValue, map_sub,
      Finsupp.linearCombination_single, one_smul, Subgroup.coe_mul, map_mul,
      Module.End.mul_apply, apartmentCyclicGenerator_action solution, sub_self]
  · simp only [apartmentRelation, apartmentSymbolValue, map_add,
      Finsupp.linearCombination_single, one_smul, Subgroup.coe_mul, map_mul,
      Module.End.mul_apply, apartmentSwapGenerator_action solution, map_neg, neg_add_cancel]

theorem polynomialFunctional_exists_of_apartmentPresentation
    (apartments_generate : Function.Surjective apartmentPresentationMap)
    (relations_complete : apartmentPresentationMap.ker ≤ apartmentRelations)
    {degree : ℕ} {polynomial : HomogeneousPoly degree} (solution : SymmetricSolution polynomial) :
    ∃ functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree,
      IsPolynomialFunctional polynomial functional := by
  let quotient_equiv : (ApartmentSymbols ⧸ apartmentPresentationMap.ker) ≃ₗ[ℂ] goodCycleModule :=
    @LinearMap.quotKerEquivOfSurjective ℂ ApartmentSymbols goodCycleModule
      inferInstance inferInstance (Submodule.addCommGroup goodCycleModule)
      inferInstance (Submodule.module goodCycleModule) apartmentPresentationMap apartments_generate
  let value_map := apartmentPresentationMap.ker.liftQ (apartmentSymbolValue polynomial)
    (relations_complete.trans (apartmentRelations_le_valueKernel solution))
  let cycle_map : goodCycleModule →ₗ[ℂ] HomogeneousPoly degree :=
    value_map.comp quotient_equiv.symm.toLinearMap
  have cycle_value (symbols : ApartmentSymbols) :
      cycle_map (apartmentPresentationMap symbols) = apartmentSymbolValue polynomial symbols := by
    have forward : quotient_equiv (Submodule.Quotient.mk symbols) =
        apartmentPresentationMap symbols := rfl
    have inverse : quotient_equiv.symm (apartmentPresentationMap symbols) =
        Submodule.Quotient.mk symbols := by
      rw [← forward, LinearEquiv.symm_apply_apply]
    change value_map (quotient_equiv.symm (apartmentPresentationMap symbols)) = _
    rw [inverse]
    rfl
  apply polynomialFunctional_exists_of_referenceCycleMap polynomial cycle_map
  · intro matrix chain
    obtain ⟨symbols, rfl⟩ := apartments_generate chain
    rw [← apartmentPresentationMap_translate, cycle_value, cycle_value,
      apartmentSymbolValue_translate]
  · have reference : apartmentPresentationMap (Finsupp.single 1 1) = referenceApartment := by
      simp only [apartmentPresentationMap, Finsupp.linearCombination_single, one_smul,
        translateGoodCycle_one]
    change cycle_map referenceApartment = _
    rw [← reference, cycle_value]
    simp only [apartmentSymbolValue, Finsupp.linearCombination_single, one_smul,
      Subgroup.coe_one, map_one, Module.End.one_apply]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
