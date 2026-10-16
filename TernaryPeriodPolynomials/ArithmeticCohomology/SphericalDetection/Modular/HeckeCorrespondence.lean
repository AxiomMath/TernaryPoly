module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.ArithmeticPeriodMap
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Representatives

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance modularHeckePrimeFact (prime : Nat.Primes) : Fact prime.val.Prime := ⟨prime.property⟩

def modularHeckeMatrix (prime : Nat.Primes) : Option (Fin prime.val) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(prime.val : ℤ), 0; 0, 1]
  | some index => !![1, (index.val : ℤ); 0, (prime.val : ℤ)]

theorem modularHeckeMatrix_det (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    (modularHeckeMatrix prime index).det = prime.val := by
  cases index <;> simp [modularHeckeMatrix, Matrix.det_fin_two]

theorem modularHeckeMatrix_rational (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    (modularHeckeMatrix prime index).map (Int.castRingHom ℚ) = (binaryHeckeRepresentative prime index).val := by
  cases index with
  | none =>
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [modularHeckeMatrix, binaryHeckeRepresentative, binaryHeckeDilate, Matrix.map]
  | some index =>
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [modularHeckeMatrix, binaryHeckeRepresentative, binaryHeckeTranslate, Matrix.map]

theorem modularHeckeMatrix_reduce (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    (Int.castRingHom (ZMod prime.val)).mapMatrix (modularHeckeMatrix prime index) =
      residueHeckeMatrix (index.map (fun value => (value.val : ZMod prime.val))) := by
  cases index with
  | none =>
    ext row column
    fin_cases row <;> fin_cases column <;> simp [modularHeckeMatrix, residueHeckeMatrix]
  | some index =>
    ext row column
    fin_cases row <;> fin_cases column <;> simp [modularHeckeMatrix, residueHeckeMatrix]

def modularHeckePermutation (prime : Nat.Primes) (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    Equiv.Perm (Option (Fin prime.val)) :=
  ((binaryHeckeIndexEquiv prime).trans
    (MulAction.toPerm (GeneralLinearGroup.map (Int.castRingHom (ZMod prime.val))
      (SpecialLinearGroup.toGL matrix)))).trans (binaryHeckeIndexEquiv prime).symm

theorem modularHeckePermutation_spec (prime : Nat.Primes) (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (index : Option (Fin prime.val)) :
    GeneralLinearGroup.map (Int.castRingHom (ZMod prime.val)) (SpecialLinearGroup.toGL matrix) •
      binaryHeckeIndexEquiv prime index =
        binaryHeckeIndexEquiv prime (modularHeckePermutation prime matrix index) := by
  simp [modularHeckePermutation]

theorem modularHecke_transition_divisible (prime : Nat.Primes) (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (index : Option (Fin prime.val)) (row column : Fin 2) :
    (prime.val : ℤ) ∣ (modularHeckeMatrix prime (modularHeckePermutation prime matrix index) *
      matrix.val * (modularHeckeMatrix prime index).adjugate) row column := by
  have residue : (Int.castRingHom (ZMod prime.val)).mapMatrix
      (modularHeckeMatrix prime (modularHeckePermutation prime matrix index) *
        matrix.val * (modularHeckeMatrix prime index).adjugate) = 0 := by
    rw [map_mul, map_mul, RingHom.map_adjugate, modularHeckeMatrix_reduce, modularHeckeMatrix_reduce]
    apply residueHeckeMatrix_transition (GeneralLinearGroup.map (Int.castRingHom (ZMod prime.val))
      (SpecialLinearGroup.toGL matrix))
    simpa only [binaryHeckeIndexEquiv_eq_point] using modularHeckePermutation_spec prime matrix index
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ prime.val).mp
  exact congrArg (fun matrix : Matrix (Fin 2) (Fin 2) (ZMod prime.val) => matrix row column) residue

theorem modularHecke_exists_transition (prime : Nat.Primes) (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (index : Option (Fin prime.val)) :
    ∃ transition : SpecialLinearGroup (Fin 2) ℤ,
      modularHeckeMatrix prime (modularHeckePermutation prime matrix index) * matrix.val =
        transition.val * modularHeckeMatrix prime index := by
  let numerator := modularHeckeMatrix prime (modularHeckePermutation prime matrix index) *
    matrix.val * (modularHeckeMatrix prime index).adjugate
  choose quotient_values quotient_eq using modularHecke_transition_divisible prime matrix index
  let quotient : Matrix (Fin 2) (Fin 2) ℤ := quotient_values
  have numerator_eq : numerator = (prime.val : ℤ) • quotient := by
    ext row column
    exact quotient_eq row column
  have numerator_det : numerator.det = (prime.val : ℤ) ^ 2 := by
    simp only [numerator, Matrix.det_mul, modularHeckeMatrix_det, matrix.property,
      Matrix.det_adjugate, Fintype.card_fin, Nat.reduceSub, pow_one, mul_one, pow_two]
  have quotient_det : quotient.det = 1 := by
    rw [numerator_eq, Matrix.det_smul, Fintype.card_fin] at numerator_det
    apply mul_left_cancel₀ (pow_ne_zero 2 (by exact_mod_cast prime.property.ne_zero) : (prime.val : ℤ) ^ 2 ≠ 0)
    simpa only [mul_one] using numerator_det
  refine ⟨⟨quotient, quotient_det⟩, ?_⟩
  have multiplied : numerator * modularHeckeMatrix prime index =
      (prime.val : ℤ) • (modularHeckeMatrix prime (modularHeckePermutation prime matrix index) * matrix.val) := by
    dsimp only [numerator]
    rw [Matrix.mul_assoc, Matrix.adjugate_mul, modularHeckeMatrix_det, Matrix.mul_smul, mul_one]
  rw [numerator_eq, Matrix.smul_mul] at multiplied
  ext row column
  apply mul_left_cancel₀ (by exact_mod_cast prime.property.ne_zero : (prime.val : ℤ) ≠ 0)
  exact (congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℤ => matrix row column) multiplied).symm

def modularHeckeTransition (prime : Nat.Primes) (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (index : Option (Fin prime.val)) : SpecialLinearGroup (Fin 2) ℤ :=
  (modularHecke_exists_transition prime matrix index).choose

theorem modularHeckeTransition_matrix (prime : Nat.Primes) (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (index : Option (Fin prime.val)) :
    modularHeckeMatrix prime (modularHeckePermutation prime matrix index) * matrix.val =
      (modularHeckeTransition prime matrix index).val * modularHeckeMatrix prime index :=
  (modularHecke_exists_transition prime matrix index).choose_spec

theorem modularHeckeTransition_rational (prime : Nat.Primes) (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (index : Option (Fin prime.val)) :
    binaryHeckeRepresentative prime (modularHeckePermutation prime matrix index) *
      GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix) =
    GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL (modularHeckeTransition prime matrix index)) *
      binaryHeckeRepresentative prime index := by
  apply Units.ext
  have relation := congrArg ((Int.castRingHom ℚ).mapMatrix) (modularHeckeTransition_matrix prime matrix index)
  rw [map_mul, map_mul] at relation
  change (modularHeckeMatrix prime (modularHeckePermutation prime matrix index)).map (Int.castRingHom ℚ) *
    matrix.val.map (Int.castRingHom ℚ) =
      (modularHeckeTransition prime matrix index).val.map (Int.castRingHom ℚ) *
        (modularHeckeMatrix prime index).map (Int.castRingHom ℚ) at relation
  rw [modularHeckeMatrix_rational, modularHeckeMatrix_rational] at relation
  exact relation

end TernaryPeriodPolynomials.SphericalDetection.Helpers
