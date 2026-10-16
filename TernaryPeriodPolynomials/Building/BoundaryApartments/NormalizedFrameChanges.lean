module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.Quotient

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

def normalizedFrameChanges : Subgroup IntegralGL3 where
  carrier := {matrix | (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* (reductionThree matrix).val = fun _ => 1}
  one_mem' := by simp
  mul_mem' := by
    intro first second first_fixed second_fixed
    change (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* (reductionThree (first * second)).val = _
    rw [map_mul, GeneralLinearGroup.coe_mul, ← Matrix.vecMul_vecMul, first_fixed, second_fixed]
  inv_mem' := by
    intro matrix fixed
    change (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* (reductionThree matrix⁻¹).val = _
    calc
      _ = ((fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* (reductionThree matrix).val) ᵥ*
          (reductionThree matrix⁻¹).val := by rw [fixed]
      _ = _ := by rw [Matrix.vecMul_vecMul, ← GeneralLinearGroup.coe_mul, ← map_mul,
        mul_inv_cancel, map_one, GeneralLinearGroup.coe_one, Matrix.vecMul_one]

def normalizedFrameChangeMap : normalizedFrameChanges →* rationalLevel where
  toFun matrix := integralImage (frameConjugate matrix.val)
    (frameConjugate_arithmetic matrix.val matrix.property)
  map_one' := by
    apply Subtype.ext
    change GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate 1) = 1
    simp [frameConjugate]
  map_mul' first second := by
    apply Subtype.ext
    change GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate (first.val * second.val)) =
      GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate first.val) *
        GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate second.val)
    rw [← map_mul]
    congr 1
    simp only [frameConjugate, mul_assoc, inv_mul_cancel_left]

def normalizedNorm : normalizedFrameChanges := ⟨integralNormGenerator, normGenerator_covector⟩
def normalizedCyclic : normalizedFrameChanges := ⟨integralCyclicGenerator, cyclicGenerator_covector⟩
def normalizedSwap : normalizedFrameChanges := ⟨integralSwapGenerator, swapGenerator_covector⟩

theorem normalizedFrameChangeMap_norm : normalizedFrameChangeMap normalizedNorm =
    apartmentNormGenerator := rfl

theorem normalizedFrameChangeMap_cyclic : normalizedFrameChangeMap normalizedCyclic =
    apartmentCyclicGenerator := rfl

theorem normalizedFrameChangeMap_swap : normalizedFrameChangeMap normalizedSwap =
    apartmentSwapGenerator := rfl

def frameChangeClass (base : rationalLevel) (matrix : normalizedFrameChanges) : ApartmentQuotient :=
  apartmentClass (base * normalizedFrameChangeMap matrix)

theorem frameChangeClass_norm (base : rationalLevel) (matrix : normalizedFrameChanges) :
    frameChangeClass base matrix + frameChangeClass base (matrix * normalizedNorm) +
      frameChangeClass base ((matrix * normalizedNorm) * normalizedNorm) = 0 := by
  have norm := apartmentClass_norm (base * normalizedFrameChangeMap matrix)
  simpa only [frameChangeClass, map_mul, normalizedFrameChangeMap_norm, pow_two, mul_assoc] using norm

theorem frameChangeClass_cyclic (base : rationalLevel) (matrix : normalizedFrameChanges) :
    frameChangeClass base (matrix * normalizedCyclic) = frameChangeClass base matrix := by
  have cyclic := apartmentClass_cyclic (base * normalizedFrameChangeMap matrix)
  simpa only [frameChangeClass, map_mul, normalizedFrameChangeMap_cyclic, mul_assoc] using cyclic

theorem frameChangeClass_swap (base : rationalLevel) (matrix : normalizedFrameChanges) :
    frameChangeClass base (matrix * normalizedSwap) = -frameChangeClass base matrix := by
  have swap := apartmentClass_swap (base * normalizedFrameChangeMap matrix)
  simpa only [frameChangeClass, map_mul, normalizedFrameChangeMap_swap, mul_assoc] using swap

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
