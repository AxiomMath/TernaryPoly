module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SmithMatrices
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RationalSmith

def diagonalUnit {R : Type} [CommRing R] {size : ℕ}
    (entries : Fin size → Rˣ) : GeneralLinearGroup (Fin size) R where
  val := Matrix.diagonal (fun index => (entries index).val)
  inv := Matrix.diagonal (fun index => (entries index).inv)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

theorem diagonalUnit_det {R : Type} [CommRing R] {size : ℕ} (entries : Fin size → Rˣ) :
    GeneralLinearGroup.det (diagonalUnit entries) = ∏ index, entries index := by
  apply Units.ext
  simp [diagonalUnit, GeneralLinearGroup.det, Matrix.det_diagonal]

theorem map_diagonalUnit {R S : Type} [CommRing R] [CommRing S] {size : ℕ}
    (hom : R →+* S) (entries : Fin size → Rˣ) :
    GeneralLinearGroup.map hom (diagonalUnit entries) =
      diagonalUnit (fun index => Units.map hom.toMonoidHom (entries index)) := by
  apply GeneralLinearGroup.ext
  intro row column
  simp [diagonalUnit, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem diagonalUnit_commute {R : Type} [CommRing R] {size : ℕ}
    (first second : Fin size → Rˣ) :
    diagonalUnit first * diagonalUnit second = diagonalUnit second * diagonalUnit first := by
  apply Units.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext index
  exact mul_comm _ _

theorem clear_denominators {size : ℕ} (matrix : Matrix (Fin size) (Fin size) ℚ) :
    ∃ denominator : ℤ, denominator ≠ 0 ∧
      ∃ integerMatrix : Matrix (Fin size) (Fin size) ℤ,
        integerMatrix.map (Int.castRingHom ℚ) = (denominator : ℚ) • matrix := by
  obtain ⟨denominator, integral⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun index : Fin size × Fin size => matrix index.1 index.2)
  have entries : ∀ row column, ∃ integer : ℤ,
      (integer : ℚ) = (denominator.val : ℚ) * matrix row column := by
    intro row column
    obtain ⟨integer, equality⟩ := integral (row, column)
    refine ⟨integer, ?_⟩
    simpa only [Algebra.smul_def, algebraMap_int_eq, Int.coe_castRingHom] using equality
  choose integers equality using entries
  refine ⟨denominator.val, mem_nonZeroDivisors_iff_ne_zero.mp denominator.property,
    integers, ?_⟩
  exact funext (fun row => funext (fun column => equality row column))

theorem rational_smith {size : ℕ} (element : GeneralLinearGroup (Fin size) ℚ) :
    ∃ left right : GeneralLinearGroup (Fin size) ℤ, ∃ entries : Fin size → ℚˣ,
      element = GeneralLinearGroup.map (Int.castRingHom ℚ) left * diagonalUnit entries *
        (GeneralLinearGroup.map (Int.castRingHom ℚ) right)⁻¹ := by
  obtain ⟨denominator, denominatorNonzero, integerMatrix, integerEquality⟩ :=
    clear_denominators element.val
  have denominatorRationalNonzero : (denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr denominatorNonzero
  have scaledDetNonzero : (integerMatrix.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [integerEquality, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ denominatorRationalNonzero) (GeneralLinearGroup.det_ne_zero element)
  have integerDetNonzero : integerMatrix.det ≠ 0 := by
    intro vanishes
    apply scaledDetNonzero
    calc
      (integerMatrix.map (Int.castRingHom ℚ)).det = (Int.castRingHom ℚ) integerMatrix.det :=
        ((Int.castRingHom ℚ).map_det integerMatrix).symm
      _ = 0 := by rw [vanishes, map_zero]
  obtain ⟨left, right, diagonal, diagonalNonzero, smith⟩ :=
    SmithMatrices.full_rank_smith integerMatrix integerDetNonzero
  let entries : Fin size → ℚˣ := fun index => Units.mk0 ((diagonal index : ℚ) / denominator)
    (div_ne_zero (Int.cast_ne_zero.mpr (diagonalNonzero index)) denominatorRationalNonzero)
  refine ⟨left, right, entries, ?_⟩
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Units.ext
  have mapped := congrArg (fun matrix : Matrix (Fin size) (Fin size) ℤ =>
    matrix.map (Int.castRingHom ℚ)) smith
  rw [Matrix.map_mul, Matrix.map_mul, integerEquality] at mapped
  rw [Matrix.diagonal_map (map_zero (Int.castRingHom ℚ))] at mapped
  have scaled := congrArg (fun matrix : Matrix (Fin size) (Fin size) ℚ =>
    (denominator : ℚ)⁻¹ • matrix) mapped
  rw [Matrix.smul_mul, smul_smul, inv_mul_cancel₀ denominatorRationalNonzero, one_smul] at scaled
  rw [← Matrix.mul_smul, ← Matrix.diagonal_smul] at scaled
  change element.val * right.val.map (Int.castRingHom ℚ) =
    left.val.map (Int.castRingHom ℚ) * Matrix.diagonal (fun index => (entries index).val)
  rw [scaled]
  congr 2
  funext index
  change (denominator : ℚ)⁻¹ * (diagonal index : ℚ) = (diagonal index : ℚ) / denominator
  rw [div_eq_mul_inv, mul_comm]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RationalSmith
