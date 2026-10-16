module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.GroupTheory.Index

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.BoundaryFiniteness.IntegralConjugation

noncomputable section

def integerMatrixMap : Matrix (Fin 3) (Fin 3) ℤ →+* Matrix (Fin 3) (Fin 3) ℚ :=
  (Int.castRingHom ℚ).mapMatrix

theorem integerMatrixMap_injective : Function.Injective integerMatrixMap :=
  Matrix.map_injective Int.cast_injective

theorem clear_denominator (matrix : Matrix (Fin 3) (Fin 3) ℚ) :
    (matrix.den : ℚ) • matrix = integerMatrixMap matrix.num := by
  have nonzero : (matrix.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr matrix.den_ne_zero
  have equality := congrArg (fun value => (matrix.den : ℚ) • value)
    matrix.inv_denom_smul_num
  simpa [integerMatrixMap, smul_smul, nonzero] using equality.symm

def congruenceModulus (matrix : RationalGL3) : ℕ :=
  3 * matrix.val.den * (matrix⁻¹).val.den

theorem congruenceModulus_ne_zero (matrix : RationalGL3) : congruenceModulus matrix ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by decide) matrix.val.den_ne_zero) (matrix⁻¹).val.den_ne_zero

theorem congruence_expansion (modulus : ℕ) (matrix : IntegralGL3)
    (congruence : Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod modulus)) matrix = 1) :
    ∃ adjustment : Matrix (Fin 3) (Fin 3) ℤ,
      matrix.val = 1 + (modulus : ℤ) • adjustment := by
  have divisibility (row column : Fin 3) :
      (modulus : ℤ) ∣ matrix.val row column - (1 : Matrix (Fin 3) (Fin 3) ℤ) row column := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ modulus).mp
    have entry := congrArg
      (fun value : Matrix.GeneralLinearGroup (Fin 3) (ZMod modulus) => value.val row column)
      congruence
    change (matrix.val row column : ZMod modulus) =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod modulus)) row column at entry
    simpa [Matrix.one_apply, sub_eq_zero] using entry
  choose adjustment specification using divisibility
  refine ⟨adjustment, ?_⟩
  ext row column
  change matrix.val row column = (1 : Matrix (Fin 3) (Fin 3) ℤ) row column +
    (modulus : ℤ) * adjustment row column
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp (specification row column))

theorem integerMatrixMap_smul (scalar : ℤ) (matrix : Matrix (Fin 3) (Fin 3) ℤ) :
    integerMatrixMap (scalar • matrix) = (scalar : ℚ) • integerMatrixMap matrix := by
  ext row column
  exact Int.cast_mul scalar (matrix row column)

theorem conjugate_expansion (matrix : RationalGL3)
    (adjustment : Matrix (Fin 3) (Fin 3) ℤ) :
    (matrix⁻¹).val * (1 + (congruenceModulus matrix : ℚ) • integerMatrixMap adjustment) *
        matrix.val =
      integerMatrixMap (1 + (3 : ℤ) • ((matrix⁻¹).val.num * adjustment * matrix.val.num)) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, matrix.inv_mul,
    map_add, map_one, integerMatrixMap_smul]
  congr 1
  calc
    _ = (3 : ℚ) • (((((matrix⁻¹).val.den : ℚ) • (matrix⁻¹).val) *
        integerMatrixMap adjustment) * ((matrix.val.den : ℚ) • matrix.val)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      congr 1
      simp only [congruenceModulus, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ = _ := by
      rw [clear_denominator, clear_denominator, map_mul, map_mul]
      simp only [Int.cast_ofNat]

theorem integral_lift (matrix : RationalGL3)
    (value inverse : Matrix (Fin 3) (Fin 3) ℤ)
    (value_spec : integerMatrixMap value = matrix.val)
    (inverse_spec : integerMatrixMap inverse = (matrix⁻¹).val) :
    ∃ lift : IntegralGL3, lift.val = value ∧
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) lift = matrix := by
  have value_inverse : value * inverse = 1 := by
    apply integerMatrixMap_injective
    rw [map_mul, map_one, value_spec, inverse_spec]
    exact matrix.mul_inv
  have inverse_value : inverse * value = 1 := by
    apply integerMatrixMap_injective
    rw [map_mul, map_one, value_spec, inverse_spec]
    exact matrix.inv_mul
  let lift : IntegralGL3 := ⟨value, inverse, value_inverse, inverse_value⟩
  refine ⟨lift, rfl, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  exact congrArg (fun entry => entry row column) value_spec

theorem reductionThree_eq_one (matrix : IntegralGL3)
    (adjustment : Matrix (Fin 3) (Fin 3) ℤ)
    (expansion : matrix.val = 1 + (3 : ℤ) • adjustment) : reductionThree matrix = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  change (matrix.val row column : ZMod 3) =
    (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) row column
  rw [expansion]
  change (((1 : Matrix (Fin 3) (Fin 3) ℤ) row column +
    (3 : ℤ) * adjustment row column : ℤ) : ZMod 3) = _
  have three_zero : (3 : ZMod 3) = 0 := by decide
  simp [Matrix.one_apply, three_zero]

theorem conjugate_mem_rationalLevel (matrix : RationalGL3) (integral : IntegralGL3)
    (congruence : Matrix.GeneralLinearGroup.map
      (Int.castRingHom (ZMod (congruenceModulus matrix))) integral = 1) :
    matrix⁻¹ * Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) integral * matrix ∈
      rationalLevel := by
  obtain ⟨adjustment, expansion⟩ := congruence_expansion (congruenceModulus matrix) integral
    congruence
  have inverse_congruence : Matrix.GeneralLinearGroup.map
      (Int.castRingHom (ZMod (congruenceModulus matrix))) integral⁻¹ = 1 := by
    rw [map_inv, congruence, inv_one]
  obtain ⟨inverse_adjustment, inverse_expansion⟩ :=
    congruence_expansion (congruenceModulus matrix) integral⁻¹ inverse_congruence
  have cast_expansion : integerMatrixMap integral.val =
      1 + (congruenceModulus matrix : ℚ) • integerMatrixMap adjustment := by
    rw [expansion, map_add, map_one, integerMatrixMap_smul, Int.cast_natCast]
  have cast_inverse_expansion : integerMatrixMap (integral⁻¹).val =
      1 + (congruenceModulus matrix : ℚ) • integerMatrixMap inverse_adjustment := by
    rw [inverse_expansion, map_add, map_one, integerMatrixMap_smul, Int.cast_natCast]
  let conjugate := matrix⁻¹ * Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) integral * matrix
  let value := 1 + (3 : ℤ) • ((matrix⁻¹).val.num * adjustment * matrix.val.num)
  let inverse := 1 + (3 : ℤ) • ((matrix⁻¹).val.num * inverse_adjustment * matrix.val.num)
  have value_spec : integerMatrixMap value = conjugate.val := by
    change integerMatrixMap value =
      (matrix⁻¹).val * integerMatrixMap integral.val * matrix.val
    rw [cast_expansion]
    exact (conjugate_expansion matrix adjustment).symm
  have inverse_identity : conjugate⁻¹ =
      matrix⁻¹ * Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) integral⁻¹ * matrix := by
    simp only [conjugate, mul_inv_rev, inv_inv, map_inv, mul_assoc]
  have inverse_spec : integerMatrixMap inverse = (conjugate⁻¹).val := by
    rw [inverse_identity]
    change integerMatrixMap inverse =
      (matrix⁻¹).val * integerMatrixMap (integral⁻¹).val * matrix.val
    rw [cast_inverse_expansion]
    exact (conjugate_expansion matrix inverse_adjustment).symm
  obtain ⟨lift, lift_value, lift_spec⟩ := integral_lift conjugate value inverse value_spec inverse_spec
  have lift_level : lift ∈ arithmeticLevel := by
    change reductionThree lift ∈ rowStabilizer
    rw [reductionThree_eq_one lift _ lift_value]
    exact rowStabilizer.one_mem
  exact ⟨⟨lift, lift_level⟩, lift_spec⟩

end

end TernaryPeriodPolynomials.BoundaryFiniteness.IntegralConjugation
