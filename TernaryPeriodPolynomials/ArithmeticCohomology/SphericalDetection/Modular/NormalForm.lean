module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G : Type*} [Group G]

def modularBlockWord (first second : G) : List (Fin 2) → G
  | [] => 1
  | head :: tail => (first * second ^ (head.val + 1)) * modularBlockWord first second tail

def modularNormalValue (first second central : G) (power : ℕ) (head : Fin 3)
    (blocks : List (Fin 2)) (tail : Fin 2) : G :=
  central ^ power * second ^ head.val * modularBlockWord first second blocks * first ^ tail.val

def HasModularNormalForm (first second central element : G) : Prop :=
  ∃ power head blocks tail, element = modularNormalValue first second central power head blocks tail

theorem modularNormalForm_one (first second central : G) : HasModularNormalForm first second central 1 := by
  refine ⟨0, 0, [], 0, ?_⟩
  simp [modularNormalValue, modularBlockWord]

theorem modularNormalForm_first (first second central : G) (square : first ^ 2 = central)
    (commutes : Commute central first) {element : G} (normal : HasModularNormalForm first second central element) :
    HasModularNormalForm first second central (first * element) := by
  obtain ⟨power, head, blocks, tail, rfl⟩ := normal
  have move : first * central ^ power = central ^ power * first := (commutes.symm.pow_right power).eq
  fin_cases head
  · cases blocks with
    | nil =>
      fin_cases tail
      · refine ⟨power, 0, [], 1, ?_⟩
        simpa [modularNormalValue, modularBlockWord] using move
      · refine ⟨power + 1, 0, [], 0, ?_⟩
        simp only [modularNormalValue, modularBlockWord, Fin.val_zero,
          pow_zero, pow_one, mul_one, ← mul_assoc, move]
        rw [mul_assoc, ← pow_two, square, ← pow_succ]
    | cons block blocks =>
      refine ⟨power + 1, ⟨block.val + 1, by omega⟩, blocks, tail, ?_⟩
      simp only [modularNormalValue, modularBlockWord, pow_zero, mul_one, ← mul_assoc, move]
      rw [mul_assoc (central ^ power) first first, ← pow_two, square, ← pow_succ]
  · refine ⟨power, 0, 0 :: blocks, tail, ?_⟩
    simp only [modularNormalValue, modularBlockWord, Fin.val_zero, zero_add,
      pow_zero, pow_one, mul_one, ← mul_assoc, move]
  · refine ⟨power, 0, 1 :: blocks, tail, ?_⟩
    simp only [modularNormalValue, modularBlockWord, Fin.val_zero, Fin.val_one,
      pow_zero, mul_one, ← mul_assoc, move]

theorem modularNormalForm_second (first second central : G) (cube : second ^ 3 = central)
    (commutes : Commute central second) {element : G} (normal : HasModularNormalForm first second central element) :
    HasModularNormalForm first second central (second * element) := by
  obtain ⟨power, head, blocks, tail, rfl⟩ := normal
  have move : second * central ^ power = central ^ power * second := (commutes.symm.pow_right power).eq
  fin_cases head
  · refine ⟨power, 1, blocks, tail, ?_⟩
    simp only [modularNormalValue, Fin.val_one, pow_zero, pow_one, mul_one, ← mul_assoc, move]
  · refine ⟨power, 2, blocks, tail, ?_⟩
    simp only [modularNormalValue, pow_one, ← mul_assoc, move]
    rw [mul_assoc (central ^ power), ← pow_two]
    rfl
  · refine ⟨power + 1, 0, blocks, tail, ?_⟩
    simp only [modularNormalValue, Fin.val_zero, pow_zero, mul_one, ← mul_assoc, move]
    rw [mul_assoc (central ^ power), ← pow_succ', cube, ← pow_succ]

theorem modularNormalForm_pow_left (first second central generator : G)
    (step : ∀ element, HasModularNormalForm first second central element →
      HasModularNormalForm first second central (generator * element))
    {element : G} (normal : HasModularNormalForm first second central element) (power : ℕ) :
    HasModularNormalForm first second central (generator ^ power * element) := by
  induction power with
  | zero => simpa only [pow_zero, one_mul] using normal
  | succ power induction =>
    simpa only [pow_succ', mul_assoc] using step _ induction

/-- Normal forms for the abstract modular relations, without assuming a presentation theorem. -/
theorem modularNormalForm_of_mem_closure (first second : G)
    (fourth : first ^ 4 = 1) (relation : second ^ 3 = first ^ 2)
    {element : G} (member : element ∈ Subgroup.closure ({first, second} : Set G)) :
    HasModularNormalForm first second (first ^ 2) element := by
  have first_commutes : Commute (first ^ 2) first := (Commute.refl first).pow_left 2
  have second_commutes : Commute (first ^ 2) second := by
    rw [← relation]
    exact (Commute.refl second).pow_left 3
  have first_step (element : G) := modularNormalForm_first first second (first ^ 2) rfl first_commutes (element := element)
  have second_step (element : G) := modularNormalForm_second first second (first ^ 2) relation second_commutes (element := element)
  have sixth : second ^ 6 = 1 := by
    calc
      second ^ 6 = (second ^ 3) ^ 2 := by rw [← pow_mul]
      _ = (first ^ 2) ^ 2 := by rw [relation]
      _ = first ^ 4 := by rw [← pow_mul]
      _ = 1 := fourth
  have first_inverse : first⁻¹ = first ^ 3 := by
    apply (eq_inv_of_mul_eq_one_left ?_).symm
    simpa only [← pow_succ] using fourth
  have second_inverse : second⁻¹ = second ^ 5 := by
    apply (eq_inv_of_mul_eq_one_left ?_).symm
    simpa only [← pow_succ] using sixth
  induction member using Subgroup.closure_induction_left with
  | one => exact modularNormalForm_one first second (first ^ 2)
  | mul_left generator generator_mem element _ induction =>
    rcases generator_mem with rfl | rfl
    · exact first_step _ induction
    · exact second_step _ induction
  | inv_mul_cancel generator generator_mem element _ induction =>
    rcases generator_mem with rfl | rfl
    · rw [first_inverse]
      exact modularNormalForm_pow_left _ _ _ _ first_step induction 3
    · rw [second_inverse]
      exact modularNormalForm_pow_left _ _ _ _ second_step induction 5

end TernaryPeriodPolynomials.SphericalDetection.Helpers
