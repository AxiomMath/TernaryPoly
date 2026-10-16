module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.NormalForm

@[expose] public section


open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def modularOrderSix : SpecialLinearGroup (Fin 2) ℤ := ModularGroup.S * ModularGroup.T

theorem modularOrderSix_matrix : modularOrderSix.val = !![0, -1; 1, 1] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [modularOrderSix, SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem modularOrderSix_cube : modularOrderSix ^ 3 = ModularGroup.S ^ 2 := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [SpecialLinearGroup.coe_pow, modularOrderSix_matrix, ModularGroup.coe_S,
      pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem modularOrderFour : ModularGroup.S ^ 4 = 1 := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [SpecialLinearGroup.coe_pow, ModularGroup.coe_S, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_two]

def positiveModularBlock (block : Fin 2) : Matrix (Fin 2) (Fin 2) ℤ :=
  if block = 0 then !![1, 1; 0, 1] else !![1, 0; 1, 1]

def positiveModularWord : List (Fin 2) → Matrix (Fin 2) (Fin 2) ℤ
  | [] => 1
  | block :: blocks => positiveModularBlock block * positiveModularWord blocks

theorem positiveModularWord_bounds (blocks : List (Fin 2)) :
    1 ≤ positiveModularWord blocks 0 0 ∧ 0 ≤ positiveModularWord blocks 0 1 ∧
      0 ≤ positiveModularWord blocks 1 0 ∧ 1 ≤ positiveModularWord blocks 1 1 ∧
      (blocks.length : ℤ) ≤ positiveModularWord blocks 0 1 + positiveModularWord blocks 1 0 := by
  induction blocks with
  | nil => norm_num [positiveModularWord]
  | cons block blocks induction =>
    fin_cases block <;>
      norm_num [positiveModularWord, positiveModularBlock, Matrix.mul_apply, Fin.sum_univ_two] <;> omega

theorem positiveModularWord_eq_one_iff (blocks : List (Fin 2)) : positiveModularWord blocks = 1 ↔ blocks = [] := by
  constructor
  · intro equality
    have bounds := positiveModularWord_bounds blocks
    rw [equality] at bounds
    have bound := bounds.2.2.2.2
    simpa using bound
  · rintro rfl
    rfl

theorem modularBlock_matrix (block : Fin 2) :
    (ModularGroup.S * modularOrderSix ^ (block.val + 1)).val = -positiveModularBlock block := by
  ext row column
  fin_cases block <;> fin_cases row <;> fin_cases column <;>
    norm_num [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_pow, modularOrderSix_matrix,
      ModularGroup.coe_S, positiveModularBlock, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem modularBlockWord_matrix (blocks : List (Fin 2)) :
    (modularBlockWord ModularGroup.S modularOrderSix blocks).val =
      (-1 : ℤ) ^ blocks.length • positiveModularWord blocks := by
  induction blocks with
  | nil => simp [modularBlockWord, positiveModularWord]
  | cons block blocks induction =>
    rw [modularBlockWord, SpecialLinearGroup.coe_mul, modularBlock_matrix, induction]
    simp only [positiveModularWord, List.length_cons, Matrix.mul_smul, pow_succ',
      neg_mul, one_mul, neg_smul]

theorem modularCenter_matrix : (ModularGroup.S ^ 2).val = (-1 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [SpecialLinearGroup.coe_pow, ModularGroup.coe_S, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem modularNormalValue_matrix (power : ℕ) (head : Fin 3) (blocks : List (Fin 2)) (tail : Fin 2) :
    (modularNormalValue ModularGroup.S modularOrderSix (ModularGroup.S ^ 2) power head blocks tail).val =
      (-1 : ℤ) ^ (power + blocks.length) •
        (modularOrderSix.val ^ head.val * positiveModularWord blocks * ModularGroup.S.val ^ tail.val) := by
  simp only [modularNormalValue, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_pow,
    modularBlockWord_matrix]
  rw [← SpecialLinearGroup.coe_pow ModularGroup.S 2, modularCenter_matrix, smul_pow, one_pow]
  simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, pow_add]
  rw [mul_comm]

theorem modularNormalValue_identity (power : ℕ) (head : Fin 3) (blocks : List (Fin 2)) (tail : Fin 2)
    (identity : modularNormalValue ModularGroup.S modularOrderSix (ModularGroup.S ^ 2) power head blocks tail = 1) :
    head = 0 ∧ blocks = [] ∧ tail = 0 ∧ Even power := by
  have matrix := congrArg Subtype.val identity
  rw [modularNormalValue_matrix] at matrix
  have bounds := positiveModularWord_bounds blocks
  have entry00 := congrArg (fun value : Matrix (Fin 2) (Fin 2) ℤ => value 0 0) matrix
  have entry01 := congrArg (fun value : Matrix (Fin 2) (Fin 2) ℤ => value 0 1) matrix
  have entry10 := congrArg (fun value : Matrix (Fin 2) (Fin 2) ℤ => value 1 0) matrix
  have entry11 := congrArg (fun value : Matrix (Fin 2) (Fin 2) ℤ => value 1 1) matrix
  have positions : head = 0 ∧ tail = 0 := by
    rcases neg_one_pow_eq_or ℤ (power + blocks.length) with sign | sign <;>
      fin_cases head <;> fin_cases tail
    all_goals first
      | exact ⟨rfl, rfl⟩
      | (exfalso
         norm_num [sign, modularOrderSix_matrix, ModularGroup.coe_S, pow_succ,
           Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at entry00 entry01 entry10 entry11
         omega)
  rcases positions with ⟨rfl, rfl⟩
  have sign : (-1 : ℤ) ^ (power + blocks.length) = 1 := by
    rcases neg_one_pow_eq_or ℤ (power + blocks.length) with sign | sign
    · exact sign
    · norm_num [sign] at entry00
      omega
  have word : positiveModularWord blocks = 1 := by simpa [sign] using matrix
  have empty := (positiveModularWord_eq_one_iff blocks).mp word
  subst blocks
  refine ⟨rfl, rfl, rfl, ?_⟩
  have even := (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℤ) ≠ 1)).mp sign
  simpa using even

end TernaryPeriodPolynomials.SphericalDetection.Helpers
