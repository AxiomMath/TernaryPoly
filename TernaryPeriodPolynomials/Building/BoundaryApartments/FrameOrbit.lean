module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.FunctionalExtension

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous

def referenceFrame : IntegralGL3 :=
  ⟨!![1, 0, 0; 0, 1, 0; 1, 1, 1], !![1, 0, 0; 0, 1, 0; -1, -1, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem referenceFrame_normalized : ∀ column, (referenceFrame.val 2 column : ZMod 3) = 1 := by
  intro column
  fin_cases column <;> rfl

theorem frameTransition_arithmetic (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    frame * referenceFrame⁻¹ ∈ arithmeticLevel := by
  change lastRow ᵥ* (reductionThree (frame * referenceFrame⁻¹)).val = lastRow
  rw [map_mul, GeneralLinearGroup.coe_mul, ← Matrix.vecMul_vecMul]
  have row : lastRow ᵥ* (reductionThree frame).val = fun _ => (1 : ZMod 3) := by
    ext column
    simp only [lastRow, Matrix.single_vecMul, one_smul, reductionThree]
    exact normalized column
  rw [row]
  ext column
  fin_cases column <;>
    simp [referenceFrame, reductionThree, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three, lastRow]

def frameTransition (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) : rationalLevel :=
  integralImage (frame * referenceFrame⁻¹) (frameTransition_arithmetic frame normalized)

theorem frameTransition_reference (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    (frameTransition frame normalized).val *
      GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame =
    GeneralLinearGroup.map (Int.castRingHom ℚ) frame := by
  change GeneralLinearGroup.map (Int.castRingHom ℚ) (frame * referenceFrame⁻¹) *
    GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame = _
  rw [← map_mul, inv_mul_cancel_right]

theorem normalizedApartmentCycle_orbit (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    normalizedApartmentCycle frame normalized =
      translateGoodCycle (frameTransition frame normalized)
        (normalizedApartmentCycle referenceFrame referenceFrame_normalized) := by
  apply Subtype.ext
  change apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) =
    translateChain (frameTransition frame normalized).val
      (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame))
  rw [apartment_translate, frameTransition_reference]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
