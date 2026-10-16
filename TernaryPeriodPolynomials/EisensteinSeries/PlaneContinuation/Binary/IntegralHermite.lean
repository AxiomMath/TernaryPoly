module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.StrongApproximation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RecoverySupport
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegralRationals

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryStrongApproximation TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteIdeleReduction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoverySupport

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryIntegralHermite

theorem triangular_rational_integral (matrix : BinaryFiniteGL) (triangular : matrix.val 1 0 = 0) :
    ∃ rational : BinaryRationalGL, ∃ integral : IntegralBinaryGL,
      rational.val 1 0 = 0 ∧ matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
        GeneralLinearGroup.map integralEmbedding integral := by
  obtain ⟨first, second, firstEquality, secondEquality⟩ := triangular_diagonal_units matrix triangular
  obtain ⟨firstRational, firstIntegral, firstFactor⟩ := exists_rational_mul_integral first
  obtain ⟨secondRational, secondIntegral, secondFactor⟩ := exists_rational_mul_integral second
  let firstImage := Units.map integralEmbedding.toMonoidHom firstIntegral
  let secondImage := Units.map integralEmbedding.toMonoidHom secondIntegral
  let parameter := first.inv * matrix.val 0 1
  obtain ⟨rationalParameter, integralParameter, parameterFactor⟩ :=
    AdelicAdditiveReduction.exists_rational_add_integral (firstImage.val * parameter * secondImage.inv)
  refine ⟨diagonal firstRational secondRational * binaryUnipotent rationalParameter,
    binaryUnipotent integralParameter * diagonal firstIntegral secondIntegral, ?_, ?_⟩
  · simp [BinaryStrongApproximation.diagonal, binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  · calc
      matrix = diagonal first second * binaryUnipotent parameter :=
        triangular_factor matrix triangular first second firstEquality secondEquality
      _ = diagonal (rationalUnit firstRational) (rationalUnit secondRational) *
          (diagonal firstImage secondImage * binaryUnipotent parameter) := by
        rw [firstFactor, secondFactor, BinaryStrongApproximation.diagonal_mul, mul_assoc]
      _ = diagonal (rationalUnit firstRational) (rationalUnit secondRational) *
          ((binaryUnipotent (algebraMap ℚ FiniteAdeles rationalParameter) *
            binaryUnipotent (integralEmbedding integralParameter)) * diagonal firstImage secondImage) := by
        rw [diagonal_unipotent, parameterFactor, unipotent_add]
      _ = _ := by
        simp only [map_mul, BinaryStrongApproximation.diagonal_map, unipotent_map]
        simp only [rationalUnit, firstImage, secondImage, mul_assoc]

theorem exists_triangular_rational_integral (matrix : BinaryFiniteGL) :
    ∃ rational : BinaryRationalGL, ∃ integral : IntegralBinaryGL,
      rational.val 1 0 = 0 ∧ matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
        GeneralLinearGroup.map integralEmbedding integral := by
  obtain ⟨compactPart, triangular⟩ := BinaryFiniteTriangular.exists_triangular_integral matrix
  obtain ⟨rational, integral, zeroEntry, equality⟩ := triangular_rational_integral _ triangular
  refine ⟨rational, integral * compactPart, zeroEntry, ?_⟩
  rw [map_mul, ← mul_assoc, ← equality, inv_mul_cancel_right]

theorem integral_mul (first second : BinaryFiniteGL)
    (firstIntegral : IntegralMatrix first) (secondIntegral : IntegralMatrix second) :
    IntegralMatrix (first * second) := by
  obtain ⟨left, leftEquality⟩ := firstIntegral
  obtain ⟨right, rightEquality⟩ := secondIntegral
  exact ⟨left * right, by rw [Matrix.map_mul, leftEquality, rightEquality]; rfl⟩

theorem integral_embedded (matrix : IntegralBinaryGL) :
    IntegralMatrix (GeneralLinearGroup.map integralEmbedding matrix) := ⟨matrix.val, rfl⟩

theorem rational_entries (matrix : BinaryRationalGL)
    (integral : IntegralMatrix (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) matrix)) :
    ∃ integer : Matrix (Fin 2) (Fin 2) ℤ, integer.map (Int.castRingHom ℚ) = matrix.val := by
  obtain ⟨preimage, equality⟩ := integral
  have entry (row column : Fin 2) : ∃ integer : ℤ, matrix.val row column = integer := by
    apply (IntegralRationals.integral_iff_integer _).mp
    exact ⟨preimage row column, congrArg (fun value : Matrix (Fin 2) (Fin 2) FiniteAdeles =>
      value row column) equality⟩
  choose integer integerEquality using entry
  exact ⟨integer, Matrix.ext (fun row column => (integerEquality row column).symm)⟩

theorem exists_triangular_integer (matrix : BinaryFiniteGL) (integral : IntegralMatrix matrix) :
    ∃ rational : BinaryRationalGL, ∃ integer : Matrix (Fin 2) (Fin 2) ℤ,
      ∃ compactPart : IntegralBinaryGL,
        integer.map (Int.castRingHom ℚ) = rational.val ∧ integer 1 0 = 0 ∧
          matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
            GeneralLinearGroup.map integralEmbedding compactPart := by
  obtain ⟨rational, compactPart, triangular, equality⟩ := exists_triangular_rational_integral matrix
  have rationalIntegral : IntegralMatrix (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational) := by
    have result := integral_mul matrix (GeneralLinearGroup.map integralEmbedding compactPart⁻¹)
      integral (integral_embedded compactPart⁻¹)
    rw [equality, map_inv, mul_inv_cancel_right] at result
    exact result
  obtain ⟨integer, integerEquality⟩ := rational_entries rational rationalIntegral
  refine ⟨rational, integer, compactPart, integerEquality, ?_, equality⟩
  have zeroEntry : (integer 1 0 : ℚ) = 0 :=
    (congrArg (fun value : Matrix (Fin 2) (Fin 2) ℚ => value 1 0) integerEquality).trans triangular
  exact_mod_cast zeroEntry

abbrev NonzeroInteger := {integer : ℤ // integer ≠ 0}

def upper (first second : NonzeroInteger) (offset : ℤ) : BinaryRationalGL :=
  BinaryStrongApproximation.diagonal
    (Units.mk0 (first.val : ℚ) (by exact_mod_cast first.property))
    (Units.mk0 (second.val : ℚ) (by exact_mod_cast second.property)) *
      binaryUnipotent ((offset : ℚ) / first.val)

theorem upper_val (first second : NonzeroInteger) (offset : ℤ) :
    (upper first second offset).val = !![(first.val : ℚ), (offset : ℚ); 0, (second.val : ℚ)] := by
  have nonzero : (first.val : ℚ) ≠ 0 := by exact_mod_cast first.property
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [upper, BinaryStrongApproximation.diagonal, binaryUnipotent,
      Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem upper_add (first second : NonzeroInteger) (offset quotient : ℤ) :
    upper first second (offset + first.val * quotient) =
      upper first second offset * binaryUnipotent (quotient : ℚ) := by
  apply Units.ext
  simp only [Units.val_mul, upper_val]
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem exists_upper (matrix : BinaryFiniteGL) (integral : IntegralMatrix matrix) :
    ∃ first second : NonzeroInteger, ∃ offset : ℤ, ∃ compactPart : IntegralBinaryGL,
      matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (upper first second offset) *
        GeneralLinearGroup.map integralEmbedding compactPart := by
  obtain ⟨rational, integer, compactPart, integerEquality, triangular, equality⟩ :=
    exists_triangular_integer matrix integral
  have rationalTriangular : rational.val 1 0 = 0 := by
    rw [← integerEquality]
    change (integer 1 0 : ℚ) = 0
    rw [triangular, Int.cast_zero]
  obtain ⟨firstUnit, secondUnit, firstEquality, secondEquality⟩ :=
    triangular_diagonal_units rational rationalTriangular
  have firstNonzero : integer 0 0 ≠ 0 := by
    have rationalNonzero : (integer 0 0 : ℚ) ≠ 0 := by
      rw [show (integer 0 0 : ℚ) = rational.val 0 0 from
        congrArg (fun value : Matrix (Fin 2) (Fin 2) ℚ => value 0 0) integerEquality,
        ← firstEquality]
      exact firstUnit.ne_zero
    exact_mod_cast rationalNonzero
  have secondNonzero : integer 1 1 ≠ 0 := by
    have rationalNonzero : (integer 1 1 : ℚ) ≠ 0 := by
      rw [show (integer 1 1 : ℚ) = rational.val 1 1 from
        congrArg (fun value : Matrix (Fin 2) (Fin 2) ℚ => value 1 1) integerEquality,
        ← secondEquality]
      exact secondUnit.ne_zero
    exact_mod_cast rationalNonzero
  let first : NonzeroInteger := ⟨integer 0 0, firstNonzero⟩
  let second : NonzeroInteger := ⟨integer 1 1, secondNonzero⟩
  have rationalEquality : rational = upper first second (integer 0 1) := by
    apply Units.ext
    rw [← integerEquality, upper_val]
    apply Matrix.ext
    intro row column
    fin_cases row <;> fin_cases column <;> simp [first, second, triangular]
  exact ⟨first, second, integer 0 1, compactPart, rationalEquality ▸ equality⟩

abbrev Index := Σ first : NonzeroInteger, NonzeroInteger × Fin first.val.natAbs

def representative (index : Index) : BinaryFiniteGL :=
  GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
    (upper index.1 index.2.1 index.2.2.val)

theorem exists_representative (matrix : BinaryFiniteGL) (integral : IntegralMatrix matrix) :
    ∃ index : Index, ∃ compactPart : IntegralBinaryGL,
      matrix = representative index * GeneralLinearGroup.map integralEmbedding compactPart := by
  obtain ⟨first, second, offset, compactPart, equality⟩ := exists_upper matrix integral
  let residue : Fin first.val.natAbs := ⟨(offset % first.val).toNat, by
    have nonnegative := Int.emod_nonneg offset first.property
    have bound := Int.emod_lt offset first.property
    omega⟩
  have offsetEquality : offset = (residue.val : ℤ) + first.val * (offset / first.val) := by
    have remainder := Int.emod_add_mul_ediv offset first.val
    dsimp only [residue]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg offset first.property)]
    exact remainder.symm
  have reduction := upper_add first second (residue.val : ℤ) (offset / first.val)
  rw [← offsetEquality] at reduction
  refine ⟨⟨first, second, residue⟩,
    binaryUnipotent ((offset / first.val : ℤ) : IntegralAdeles) * compactPart, ?_⟩
  rw [equality, reduction, map_mul, map_mul, mul_assoc]
  unfold representative
  congr 2
  simp only [unipotent_map, map_intCast]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryIntegralHermite
