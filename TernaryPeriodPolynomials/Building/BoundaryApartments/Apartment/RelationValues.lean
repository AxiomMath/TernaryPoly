module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.FrameNormalization
public import TernaryPeriodPolynomials.Building.BoundaryApartments.BoundaryDetection

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

def integralNormGenerator : IntegralGL3 :=
  ⟨!![0, -1, 0; 1, -1, 0; 0, 0, 1], !![-1, 1, 0; -1, 0, 0; 0, 0, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def integralSwapGenerator : IntegralGL3 :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def integralCyclicGenerator : IntegralGL3 :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def frameConjugate (matrix : IntegralGL3) : IntegralGL3 := referenceFrame * matrix * referenceFrame⁻¹

theorem frameConjugate_arithmetic (matrix : IntegralGL3)
    (covector_fixed : (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* (reductionThree matrix).val = fun _ => 1) :
    frameConjugate matrix ∈ arithmeticLevel := by
  apply frameTransition_arithmetic (referenceFrame * matrix)
  intro column
  have row := congrFun covector_fixed column
  change ((referenceFrame.val * matrix.val) 2 column : ZMod 3) = 1
  simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul]
  have reference_row (index : Fin 3) : (referenceFrame.val 2 index : ZMod 3) = 1 :=
    referenceFrame_normalized index
  simp only [reference_row, one_mul]
  simp only [Matrix.vecMul, dotProduct, one_mul] at row
  have entries (index : Fin 3) : (reductionThree matrix).val index column =
      (matrix.val index column : ZMod 3) := rfl
  simpa only [entries] using row

theorem normGenerator_covector :
    (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* (reductionThree integralNormGenerator).val = fun _ => 1 := by
  ext column
  fin_cases column <;>
    simp [integralNormGenerator, reductionThree, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  decide

theorem swapGenerator_covector :
    (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* (reductionThree integralSwapGenerator).val = fun _ => 1 := by
  ext column
  fin_cases column <;>
    simp [integralSwapGenerator, reductionThree, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem cyclicGenerator_covector :
    (fun _ : Fin 3 => (1 : ZMod 3)) ᵥ* (reductionThree integralCyclicGenerator).val = fun _ => 1 := by
  ext column
  fin_cases column <;>
    simp [integralCyclicGenerator, reductionThree, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

def apartmentNormGenerator : rationalLevel :=
  integralImage (frameConjugate integralNormGenerator)
    (frameConjugate_arithmetic integralNormGenerator normGenerator_covector)

def apartmentSwapGenerator : rationalLevel :=
  integralImage (frameConjugate integralSwapGenerator)
    (frameConjugate_arithmetic integralSwapGenerator swapGenerator_covector)

def apartmentCyclicGenerator : rationalLevel :=
  integralImage (frameConjugate integralCyclicGenerator)
    (frameConjugate_arithmetic integralCyclicGenerator cyclicGenerator_covector)

theorem normGenerator_cube : integralNormGenerator ^ 3 = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [pow_succ, integralNormGenerator, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem normGenerator_norm {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) :
    polynomial + rationalCoefficientComponent degree trivialCharacter
        (GeneralLinearGroup.map (Int.castRingHom ℚ) integralNormGenerator) polynomial +
      rationalCoefficientComponent degree trivialCharacter
        (GeneralLinearGroup.map (Int.castRingHom ℚ) (integralNormGenerator ^ 2)) polynomial = 0 := by
  have determinant : (GeneralLinearGroup.det integralNormGenerator : ℤ) = 1 := by
    change integralNormGenerator.val.det = 1
    norm_num [integralNormGenerator, Matrix.det_fin_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have first_substitution :
      substitute ((GeneralLinearGroup.map (Int.castRingHom ℂ) integralNormGenerator)⁻¹).val =
      bind₁ ![X 1 - X 0, -X 0, X 2] := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [substitute, linearForm, ← map_inv, integralNormGenerator,
      Fin.sum_univ_three]; ring
  have second_substitution :
      substitute ((GeneralLinearGroup.map (Int.castRingHom ℂ) (integralNormGenerator ^ 2))⁻¹).val =
      bind₁ ![-X 1, X 0 - X 1, X 2] := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [substitute, linearForm, ← map_inv, integralNormGenerator,
      pow_two, Matrix.mul_apply, Fin.sum_univ_three]; ring
  apply Subtype.ext
  have determinant_square : (GeneralLinearGroup.det (integralNormGenerator ^ 2) : ℤ) = 1 := by
    rw [map_pow, Units.val_pow_eq_pow_val, determinant, one_pow]
  simp only [Submodule.coe_add, rationalCoefficient_integralFrame, determinant,
    determinant_square, Int.cast_one, C_1, one_mul, first_substitution, second_substitution,
    Submodule.coe_zero]
  exact (by abel : polynomial.val + bind₁ ![X 1 - X 0, -X 0, X 2] polynomial.val +
    bind₁ ![-X 1, X 0 - X 1, X 2] polynomial.val =
      polynomial.val + bind₁ ![-X 1, X 0 - X 1, X 2] polynomial.val +
        bind₁ ![X 1 - X 0, -X 0, X 2] polynomial.val).trans solution.2

theorem swapGenerator_action {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) :
    rationalCoefficientComponent degree trivialCharacter
      (GeneralLinearGroup.map (Int.castRingHom ℚ) integralSwapGenerator) polynomial =
        -polynomial := by
  have determinant : (GeneralLinearGroup.det integralSwapGenerator : ℤ) = -1 := by
    change integralSwapGenerator.val.det = -1
    norm_num [integralSwapGenerator, Matrix.det_fin_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have substitution :
      substitute ((GeneralLinearGroup.map (Int.castRingHom ℂ) integralSwapGenerator)⁻¹).val =
        bind₁ (fun index => X (Equiv.swap (0 : Fin 3) 1 index)) := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [substitute, linearForm, ← map_inv, integralSwapGenerator,
      Equiv.swap_apply_def, Fin.sum_univ_three]
  apply Subtype.ext
  rw [rationalCoefficient_integralFrame, determinant, substitution,
    solution.1 (Equiv.swap 0 1)]
  simp

def cyclicPermutation : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by intro index; fin_cases index <;> rfl
  right_inv := by intro index; fin_cases index <;> rfl

theorem cyclicGenerator_action {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) :
    rationalCoefficientComponent degree trivialCharacter
      (GeneralLinearGroup.map (Int.castRingHom ℚ) integralCyclicGenerator) polynomial =
        polynomial := by
  have determinant : (GeneralLinearGroup.det integralCyclicGenerator : ℤ) = 1 := by
    change integralCyclicGenerator.val.det = 1
    norm_num [integralCyclicGenerator, Matrix.det_fin_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have substitution :
      substitute ((GeneralLinearGroup.map (Int.castRingHom ℂ) integralCyclicGenerator)⁻¹).val =
        bind₁ (fun index => X (cyclicPermutation index)) := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [substitute, linearForm, ← map_inv, integralCyclicGenerator,
      cyclicPermutation, Fin.sum_univ_three]
  apply Subtype.ext
  rw [rationalCoefficient_integralFrame, determinant, substitution,
    solution.1 cyclicPermutation]
  simp

theorem frameConjugate_action (degree : ℕ) (matrix : IntegralGL3)
    (polynomial : HomogeneousPoly degree) :
    rationalCoefficientComponent degree trivialCharacter
        (GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate matrix))
        (framePolynomial degree referenceFrame polynomial) =
      framePolynomial degree referenceFrame
        (rationalCoefficientComponent degree trivialCharacter
          (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) polynomial) := by
  unfold framePolynomial
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul]
  simp only [frameConjugate, mul_assoc, inv_mul_cancel, mul_one, map_mul,
    Module.End.mul_apply]

theorem apartmentNormGenerator_norm {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) :
    framePolynomial degree referenceFrame polynomial +
      rationalCoefficientComponent degree trivialCharacter apartmentNormGenerator.val
        (framePolynomial degree referenceFrame polynomial) +
      rationalCoefficientComponent degree trivialCharacter (apartmentNormGenerator ^ 2).val
        (framePolynomial degree referenceFrame polynomial) = 0 := by
  have conjugate_square : (frameConjugate integralNormGenerator) ^ 2 =
      frameConjugate (integralNormGenerator ^ 2) := by
    simp [frameConjugate, pow_two, mul_assoc]
  have generator_val : apartmentNormGenerator.val =
      GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate integralNormGenerator) := rfl
  rw [Subgroup.coe_pow, generator_val, ← map_pow, conjugate_square,
    frameConjugate_action, frameConjugate_action]
  change rationalCoefficientComponent degree trivialCharacter
      (GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame) polynomial +
    rationalCoefficientComponent degree trivialCharacter
      (GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame)
        (rationalCoefficientComponent degree trivialCharacter
          (GeneralLinearGroup.map (Int.castRingHom ℚ) integralNormGenerator) polynomial) +
    rationalCoefficientComponent degree trivialCharacter
      (GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame)
        (rationalCoefficientComponent degree trivialCharacter
          (GeneralLinearGroup.map (Int.castRingHom ℚ) (integralNormGenerator ^ 2)) polynomial) = 0
  rw [← map_add, ← map_add, normGenerator_norm solution, map_zero]

theorem apartmentSwapGenerator_action {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) :
    rationalCoefficientComponent degree trivialCharacter apartmentSwapGenerator.val
      (framePolynomial degree referenceFrame polynomial) =
        -framePolynomial degree referenceFrame polynomial := by
  change rationalCoefficientComponent degree trivialCharacter
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate integralSwapGenerator))
      (framePolynomial degree referenceFrame polynomial) = _
  rw [frameConjugate_action, swapGenerator_action solution]
  exact map_neg _ _

theorem apartmentCyclicGenerator_action {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) :
    rationalCoefficientComponent degree trivialCharacter apartmentCyclicGenerator.val
      (framePolynomial degree referenceFrame polynomial) =
        framePolynomial degree referenceFrame polynomial := by
  change rationalCoefficientComponent degree trivialCharacter
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate integralCyclicGenerator))
      (framePolynomial degree referenceFrame polynomial) = _
  rw [frameConjugate_action, cyclicGenerator_action solution]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
