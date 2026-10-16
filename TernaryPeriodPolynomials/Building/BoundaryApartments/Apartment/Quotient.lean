module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.FunctionalDescent

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous

abbrev ApartmentQuotient := ApartmentSymbols ⧸ apartmentRelations

def apartmentClass (matrix : rationalLevel) : ApartmentQuotient :=
  apartmentRelations.mkQ (Finsupp.single matrix 1)

theorem apartmentClass_norm (matrix : rationalLevel) :
    apartmentClass matrix + apartmentClass (matrix * apartmentNormGenerator) +
      apartmentClass (matrix * apartmentNormGenerator ^ 2) = 0 := by
  have relation : apartmentRelation (matrix, 0) ∈ apartmentRelations :=
    Submodule.subset_span ⟨(matrix, 0), rfl⟩
  have zero := (Submodule.Quotient.mk_eq_zero apartmentRelations).mpr relation
  change apartmentRelations.mkQ (apartmentRelation (matrix, 0)) = 0 at zero
  simpa only [apartmentRelation, map_add, apartmentClass] using zero

theorem apartmentClass_cyclic (matrix : rationalLevel) :
    apartmentClass (matrix * apartmentCyclicGenerator) = apartmentClass matrix := by
  have relation : apartmentRelation (matrix, 1) ∈ apartmentRelations :=
    Submodule.subset_span ⟨(matrix, 1), rfl⟩
  have zero := (Submodule.Quotient.mk_eq_zero apartmentRelations).mpr relation
  change apartmentRelations.mkQ (apartmentRelation (matrix, 1)) = 0 at zero
  have difference : apartmentClass (matrix * apartmentCyclicGenerator) - apartmentClass matrix = 0 := by
    simpa only [apartmentRelation, map_sub, apartmentClass] using zero
  exact sub_eq_zero.mp difference

theorem apartmentClass_swap (matrix : rationalLevel) :
    apartmentClass (matrix * apartmentSwapGenerator) = -apartmentClass matrix := by
  have relation : apartmentRelation (matrix, 2) ∈ apartmentRelations :=
    Submodule.subset_span ⟨(matrix, 2), rfl⟩
  have zero := (Submodule.Quotient.mk_eq_zero apartmentRelations).mpr relation
  change apartmentRelations.mkQ (apartmentRelation (matrix, 2)) = 0 at zero
  have sum : apartmentClass (matrix * apartmentSwapGenerator) + apartmentClass matrix = 0 := by
    simpa only [apartmentRelation, map_add, apartmentClass] using zero
  exact eq_neg_of_add_eq_zero_left sum

def apartmentQuotientToCycles : ApartmentQuotient →ₗ[ℂ] goodCycleModule :=
  @Submodule.liftQ ℂ ApartmentSymbols inferInstance inferInstance inferInstance apartmentRelations
    ℂ goodCycleModule inferInstance (Submodule.addCommGroup goodCycleModule)
    (Submodule.module goodCycleModule) (RingHom.id ℂ) apartmentPresentationMap apartmentRelations_le_kernel

theorem apartmentQuotientToCycles_class (matrix : rationalLevel) :
    apartmentQuotientToCycles (apartmentClass matrix) = translateGoodCycle matrix referenceApartment := by
  change apartmentPresentationMap (Finsupp.single matrix 1) = _
  simp only [apartmentPresentationMap, Finsupp.linearCombination_single, one_smul]

theorem apartmentQuotientToCycles_surjective : Function.Surjective apartmentQuotientToCycles := by
  intro cycle
  obtain ⟨symbols, value⟩ := apartmentPresentationMap_surjective cycle
  exact ⟨apartmentRelations.mkQ symbols, value⟩

def apartmentQuotientValue {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) : ApartmentQuotient →ₗ[ℂ] HomogeneousPoly degree :=
  apartmentRelations.liftQ (apartmentSymbolValue polynomial) (apartmentRelations_le_valueKernel solution)

theorem normalizedFrame_right_mul (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) (change_frame : IntegralGL3)
    (covector : (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* (reductionThree change_frame).val = fun _ => 1) :
    ∀ column, ((frame * change_frame).val 2 column : ZMod 3) = 1 := by
  intro column
  have entry := congrFun covector column
  change ((frame.val * change_frame.val) 2 column : ZMod 3) = 1
  simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul, normalized, one_mul]
  change (∑ index, 1 * (change_frame.val index column : ZMod 3)) = 1 at entry
  simpa only [one_mul] using entry

theorem frameTransition_right_mul (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) (change_frame : IntegralGL3)
    (covector : (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* (reductionThree change_frame).val = fun _ => 1) :
    frameTransition (frame * change_frame) (normalizedFrame_right_mul frame normalized change_frame covector) =
      frameTransition frame normalized * integralImage (frameConjugate change_frame)
        (frameConjugate_arithmetic change_frame covector) := by
  apply Subtype.ext
  change GeneralLinearGroup.map (Int.castRingHom ℚ) ((frame * change_frame) * referenceFrame⁻¹) =
    GeneralLinearGroup.map (Int.castRingHom ℚ) (frame * referenceFrame⁻¹) *
      GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate change_frame)
  rw [← map_mul]
  congr 1
  simp only [frameConjugate, mul_assoc, inv_mul_cancel_left]

def normalizedApartmentClass (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) : ApartmentQuotient :=
  apartmentClass (frameTransition frame normalized)

theorem normalizedApartmentClass_norm (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    normalizedApartmentClass frame normalized +
      normalizedApartmentClass (frame * integralNormGenerator)
        (normalizedFrame_right_mul frame normalized integralNormGenerator normGenerator_covector) +
      normalizedApartmentClass ((frame * integralNormGenerator) * integralNormGenerator)
        (normalizedFrame_right_mul _
          (normalizedFrame_right_mul frame normalized integralNormGenerator normGenerator_covector)
          integralNormGenerator normGenerator_covector) = 0 := by
  simp only [normalizedApartmentClass]
  rw [frameTransition_right_mul (frame * integralNormGenerator)
    (normalizedFrame_right_mul frame normalized integralNormGenerator normGenerator_covector)
    integralNormGenerator normGenerator_covector,
    frameTransition_right_mul frame normalized integralNormGenerator normGenerator_covector]
  change apartmentClass (frameTransition frame normalized) +
    apartmentClass (frameTransition frame normalized * apartmentNormGenerator) +
    apartmentClass ((frameTransition frame normalized * apartmentNormGenerator) * apartmentNormGenerator) = 0
  simpa only [pow_two, mul_assoc] using apartmentClass_norm (frameTransition frame normalized)

theorem normalizedApartmentClass_cyclic (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    normalizedApartmentClass (frame * integralCyclicGenerator)
      (normalizedFrame_right_mul frame normalized integralCyclicGenerator cyclicGenerator_covector) =
        normalizedApartmentClass frame normalized := by
  simp only [normalizedApartmentClass]
  rw [frameTransition_right_mul frame normalized integralCyclicGenerator cyclicGenerator_covector]
  exact apartmentClass_cyclic (frameTransition frame normalized)

theorem normalizedApartmentClass_swap (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    normalizedApartmentClass (frame * integralSwapGenerator)
      (normalizedFrame_right_mul frame normalized integralSwapGenerator swapGenerator_covector) =
        -normalizedApartmentClass frame normalized := by
  simp only [normalizedApartmentClass]
  rw [frameTransition_right_mul frame normalized integralSwapGenerator swapGenerator_covector]
  exact apartmentClass_swap (frameTransition frame normalized)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
