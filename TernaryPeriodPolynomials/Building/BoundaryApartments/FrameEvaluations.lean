module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.ReflectionCoordinates

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous MvPolynomial

def firstBernoulliFrame : IntegralGL3 :=
  ⟨!![0,-1,0;0,-1,-1;1,-2,-2], !![0,-2,1;-1,0,0;1,-1,0], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]⟩

def secondBernoulliFrame : IntegralGL3 :=
  ⟨!![0,1,-2;0,0,-1;1,1,-2], !![-1,0,1;1,-2,0;0,-1,0], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]⟩

def thirdBernoulliFrame : IntegralGL3 :=
  ⟨!![0,-2,-1;0,-1,-1;1,-2,-2], !![0,-2,1;-1,1,0;1,-2,0], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]⟩

theorem firstBernoulliFrame_normalized :
    ∀ column, (firstBernoulliFrame.val 2 column : ZMod 3) = 1 := by
  intro column
  fin_cases column
  · rfl
  · change (-2 : ZMod 3) = 1
    decide
  · change (-2 : ZMod 3) = 1
    decide

theorem secondBernoulliFrame_normalized :
    ∀ column, (secondBernoulliFrame.val 2 column : ZMod 3) = 1 := by
  intro column
  fin_cases column
  · rfl
  · rfl
  · change (-2 : ZMod 3) = 1
    decide

theorem thirdBernoulliFrame_normalized :
    ∀ column, (thirdBernoulliFrame.val 2 column : ZMod 3) = 1 := by
  intro column
  fin_cases column
  · rfl
  · change (-2 : ZMod 3) = 1
    decide
  · change (-2 : ZMod 3) = 1
    decide

theorem firstBernoulliFrame_det : (GeneralLinearGroup.det firstBernoulliFrame : ℤ) = 1 := by
  change firstBernoulliFrame.val.det = 1
  norm_num [firstBernoulliFrame, Matrix.det_fin_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem secondBernoulliFrame_det : (GeneralLinearGroup.det secondBernoulliFrame : ℤ) = -1 := by
  change secondBernoulliFrame.val.det = -1
  norm_num [secondBernoulliFrame, Matrix.det_fin_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem thirdBernoulliFrame_det : (GeneralLinearGroup.det thirdBernoulliFrame : ℤ) = 1 := by
  change thirdBernoulliFrame.val.det = 1
  norm_num [thirdBernoulliFrame, Matrix.det_fin_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem firstBernoulliFrame_substitute :
    substitute ((GeneralLinearGroup.map (Int.castRingHom ℂ) firstBernoulliFrame)⁻¹).val =
      bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] := by
  apply MvPolynomial.algHom_ext
  intro index
  fin_cases index <;>
    norm_num [substitute, linearForm, ← map_inv, firstBernoulliFrame,
      GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem secondBernoulliFrame_substitute :
    substitute ((GeneralLinearGroup.map (Int.castRingHom ℂ) secondBernoulliFrame)⁻¹).val =
      bind₁ ![X 2 - X 0, X 0 - 2 * X 1, -X 1] := by
  apply MvPolynomial.algHom_ext
  intro index
  fin_cases index <;>
    norm_num [substitute, linearForm, ← map_inv, secondBernoulliFrame,
      GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem thirdBernoulliFrame_substitute :
    substitute ((GeneralLinearGroup.map (Int.castRingHom ℂ) thirdBernoulliFrame)⁻¹).val =
      bind₁ ![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] := by
  apply MvPolynomial.algHom_ext
  intro index
  fin_cases index <;>
    norm_num [substitute, linearForm, ← map_inv, thirdBernoulliFrame,
      GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem firstBernoulliFrame_evaluation {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional) :
    (functional (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) firstBernoulliFrame))).val =
      bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] polynomial.val := by
  rw [functional_property.2 firstBernoulliFrame firstBernoulliFrame_normalized,
    firstBernoulliFrame_det, firstBernoulliFrame_substitute]
  simp

theorem secondBernoulliFrame_evaluation {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional) :
    (functional (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) secondBernoulliFrame))).val =
      -(bind₁ ![X 2 - X 0, X 0 - 2 * X 1, -X 1] polynomial.val) := by
  rw [functional_property.2 secondBernoulliFrame secondBernoulliFrame_normalized,
    secondBernoulliFrame_det, secondBernoulliFrame_substitute]
  simp

theorem thirdBernoulliFrame_evaluation {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional) :
    (functional (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) thirdBernoulliFrame))).val =
      bind₁ ![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] polynomial.val := by
  rw [functional_property.2 thirdBernoulliFrame thirdBernoulliFrame_normalized,
    thirdBernoulliFrame_det, thirdBernoulliFrame_substitute]
  simp

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
