module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.NormalizedFrameChanges

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

def squareABD : normalizedFrameChanges :=
  ⟨GeneralLinearGroup.mk'' !![1,0,1;0,1,1;0,0,-1] (by norm_num [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]), by
    change (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* _ = _
    ext column
    fin_cases column <;>
      norm_num [reductionThree, GeneralLinearGroup.map_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]⟩

def squareACD : normalizedFrameChanges :=
  ⟨GeneralLinearGroup.mk'' !![1,0,1;0,0,1;0,1,-1] (by norm_num [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]), by
    change (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* _ = _
    ext column
    fin_cases column <;>
      norm_num [reductionThree, GeneralLinearGroup.map_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]⟩

def squareBCD : normalizedFrameChanges :=
  ⟨GeneralLinearGroup.mk'' !![0,0,1;1,0,1;0,1,-1] (by norm_num [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]), by
    change (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* _ = _
    ext column
    fin_cases column <;>
      norm_num [reductionThree, GeneralLinearGroup.map_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]⟩

private theorem squareACD_first_product :
    squareACD * normalizedCyclic * normalizedNorm * normalizedCyclic =
      squareABD * normalizedNorm * normalizedNorm := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [squareACD, squareABD, normalizedCyclic, normalizedNorm,
      integralCyclicGenerator, integralNormGenerator, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem squareACD_second_product :
    squareACD * normalizedCyclic * normalizedNorm * normalizedNorm * normalizedCyclic * normalizedCyclic =
      normalizedNorm * normalizedNorm * normalizedSwap := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [squareACD, normalizedCyclic, normalizedNorm, normalizedSwap,
      integralCyclicGenerator, integralNormGenerator, integralSwapGenerator,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem squareBCD_first_product :
    squareBCD * normalizedCyclic * normalizedNorm * normalizedCyclic =
      squareABD * normalizedNorm * normalizedSwap := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [squareBCD, squareABD, normalizedCyclic, normalizedNorm, normalizedSwap,
      integralCyclicGenerator, integralNormGenerator, integralSwapGenerator,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem squareBCD_second_product :
    squareBCD * normalizedCyclic * normalizedNorm * normalizedNorm * normalizedCyclic * normalizedCyclic =
      normalizedNorm := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [squareBCD, normalizedCyclic, normalizedNorm,
      integralCyclicGenerator, integralNormGenerator, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- The four unimodular faces of a square satisfy their boundary relation
already modulo the norm and permutation relations. -/
theorem frameChangeClass_square (base : rationalLevel) :
    frameChangeClass base squareBCD - frameChangeClass base squareACD +
      frameChangeClass base squareABD - frameChangeClass base 1 = 0 := by
  have first := frameChangeClass_norm base 1
  simp only [one_mul] at first
  have second := frameChangeClass_norm base squareABD
  have third := frameChangeClass_norm base (squareACD * normalizedCyclic)
  rw [frameChangeClass_cyclic] at third
  have third_first := frameChangeClass_cyclic base (squareACD * normalizedCyclic * normalizedNorm)
  rw [squareACD_first_product] at third_first
  have third_second := (frameChangeClass_cyclic base
    (squareACD * normalizedCyclic * normalizedNorm * normalizedNorm * normalizedCyclic)).trans
    (frameChangeClass_cyclic base (squareACD * normalizedCyclic * normalizedNorm * normalizedNorm))
  rw [squareACD_second_product, frameChangeClass_swap] at third_second
  rw [← third_first, ← third_second] at third
  have fourth := frameChangeClass_norm base (squareBCD * normalizedCyclic)
  rw [frameChangeClass_cyclic] at fourth
  have fourth_first := frameChangeClass_cyclic base (squareBCD * normalizedCyclic * normalizedNorm)
  rw [squareBCD_first_product, frameChangeClass_swap] at fourth_first
  have fourth_second := (frameChangeClass_cyclic base
    (squareBCD * normalizedCyclic * normalizedNorm * normalizedNorm * normalizedCyclic)).trans
    (frameChangeClass_cyclic base (squareBCD * normalizedCyclic * normalizedNorm * normalizedNorm))
  rw [squareBCD_second_product] at fourth_second
  rw [← fourth_first, ← fourth_second] at fourth
  have combined := congrArg₂ (fun x y : ApartmentQuotient => -x + y)
    (congrArg₂ (fun x y : ApartmentQuotient => x + y) first third)
    (congrArg₂ (fun x y : ApartmentQuotient => x + y) second fourth)
  convert combined using 1 <;> abel

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
