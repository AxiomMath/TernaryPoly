module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BernoulliDetection.Mixed

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open Matrix MvPolynomial

namespace TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers

def binaryIntegral (index : Fin 3) : IntegralGL3 :=
  ![⟨!![1,0,0;0,1,-1;0,3,-2], !![1,0,0;0,-2,1;0,-3,1], by
      ext row column; fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three], by
      ext row column; fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three]⟩,
    ⟨!![1,0,0;0,-1,0;0,-3,1], !![1,0,0;0,-1,0;0,-3,1], by
      ext row column; fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three], by
      ext row column; fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three]⟩,
    ⟨!![1,0,0;0,-1,0;0,0,1], !![1,0,0;0,-1,0;0,0,1], by
      ext row column; fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three], by
      ext row column; fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three]⟩] index

noncomputable def binaryRational (index : Fin 3) : RationalGL3 :=
  ![binaryA, binaryB, binaryR] index

theorem binary_integral_mem (index : Fin 3) : binaryIntegral index ∈ arithmeticLevel := by
  classical
  change lastRow ᵥ* (reductionThree (binaryIntegral index)).val = lastRow
  ext coordinate
  fin_cases index <;> fin_cases coordinate <;>
    norm_num [binaryIntegral, lastRow, reductionThree, Matrix.vecMul, Fin.sum_univ_three,
      Matrix.cons_val_two, Pi.single_apply, Fin.ext_iff]
  all_goals decide

theorem binary_integral_map (index : Fin 3) :
    GeneralLinearGroup.map (Int.castRingHom ℚ) (binaryIntegral index) = binaryRational index := by
  apply Units.ext
  ext row column
  fin_cases index <;> fin_cases row <;> fin_cases column <;>
    simp [binaryIntegral, binaryRational, binaryA, binaryB, binaryR]

theorem binary_rational_mem (index : Fin 3) : binaryRational index ∈ rationalLevel := by
  refine ⟨⟨binaryIntegral index, binary_integral_mem index⟩, ?_⟩
  exact binary_integral_map index

noncomputable def binaryLevel (index : Fin 3) : rationalLevel :=
  ⟨binaryRational index, binary_rational_mem index⟩

theorem binary_flag_fixed (index : Fin 3) :
    (binaryRational index)⁻¹ • (QuotientGroup.mk 1 : Flags .line) = QuotientGroup.mk 1 := by
  apply line_standard_flag_fixed
  change InLineParabolic (binaryRational index)
  fin_cases index <;> simp [binaryRational, binaryA, binaryB, binaryR, InLineParabolic]

def binaryFirstCoefficient (index : Fin 3) : ℤ := ![1, -1, -1] index
def binarySecondCoefficient (index : Fin 3) : ℤ := ![-1, 0, 0] index
def binaryThirdCoefficient (index : Fin 3) : ℤ := ![3, -3, 0] index
def binaryFourthCoefficient (index : Fin 3) : ℤ := ![-2, 1, 1] index

theorem binary_first_conjugate (index : Fin 3) :
    (binaryRational index)⁻¹ * lineUnipotent 1 0 * binaryRational index =
      lineUnipotent (binaryFirstCoefficient index : ℚ) (binarySecondCoefficient index : ℚ) := by
  apply Units.ext
  ext row column
  fin_cases index <;> fin_cases row <;> fin_cases column <;>
    norm_num [binaryRational, binaryA, binaryB, binaryR, lineUnipotent, upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three, binaryFirstCoefficient, binarySecondCoefficient,
      Matrix.cons_val_two]

theorem binary_second_conjugate (index : Fin 3) :
    (binaryRational index)⁻¹ * lineUnipotent 0 1 * binaryRational index =
      lineUnipotent (binaryThirdCoefficient index : ℚ) (binaryFourthCoefficient index : ℚ) := by
  apply Units.ext
  ext row column
  fin_cases index <;> fin_cases row <;> fin_cases column <;>
    norm_num [binaryRational, binaryA, binaryB, binaryR, lineUnipotent, upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three, binaryThirdCoefficient, binaryFourthCoefficient,
      Matrix.cons_val_two]

def binaryTransformedSecond (index : Fin 3) (second third : ℂ) : ℂ :=
  ![-2 * second + third, -second, -second] index

def binaryTransformedThird (index : Fin 3) (second third : ℂ) : ℂ :=
  ![-3 * second + third, -3 * second + third, third] index

def binaryScalar (index : Fin 3) : ℂ := ![1, -1, -1] index

theorem binary_specialization {degree : ℕ} (index : Fin 3)
    (polynomial : HomogeneousPoly degree) (second third : ℂ) :
    specializeFirst second third
      (rationalCoefficientComponent degree trivialCharacter (binaryRational index) polynomial).val =
    Polynomial.C (binaryScalar index) *
      specializeFirst (binaryTransformedSecond index second third)
        (binaryTransformedThird index second third) polynomial.val := by
  apply Polynomial.funext
  intro first
  rw [specializeFirst_eval, Polynomial.eval_mul, Polynomial.eval_C, specializeFirst_eval,
    rationalCoefficient_coe, action_apply]
  have determinant : determinantCharacter (-1)
      (GeneralLinearGroup.map (algebraMap ℚ ℂ) (binaryRational index)) = binaryScalar index := by
    fin_cases index <;>
      norm_num [binaryRational, binaryA, binaryB, binaryR, binaryScalar,
        determinantCharacter, GeneralLinearGroup.det, Matrix.det_fin_three,
        Matrix.cons_val_two]
  rw [determinant, Algebra.smul_def, map_mul, MvPolynomial.algebraMap_eq, eval_C]
  apply congrArg (fun value : ℂ => binaryScalar index * value)
  rw [substitute, eval_bind]
  have coordinates :
      (fun coordinate => eval ![first, second, third]
        (linearForm
          ((GeneralLinearGroup.map (algebraMap ℚ ℂ) (binaryRational index))⁻¹).val
          coordinate)) =
      ![first, binaryTransformedSecond index second third,
        binaryTransformedThird index second third] := by
    ext coordinate
    fin_cases index <;> fin_cases coordinate <;>
      simp [linearForm, ← map_inv, binaryRational, binaryA, binaryB, binaryR,
        Fin.sum_univ_three, binaryTransformedSecond, binaryTransformedThird,
        Matrix.cons_val_two]
  rw [coordinates]

theorem binary_mixed_coordinate_eval {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (primitive_eq : ∀ vertices flag, cocycle.val.val vertices =
      primitive.val ![vertices 1, vertices 2] flag -
        primitive.val ![vertices 0, vertices 2] flag +
        primitive.val ![vertices 0, vertices 1] flag)
    (pure : PureMixedBadLine cocycle) (index : Fin 3) (first second third : ℂ)
    (transformed_ne : binaryTransformedSecond index second third ≠ 0) :
    eval ![first, second, third] (mixedBernoulliCoordinate cocycle (binaryRational index)) =
      eval ![first, binaryTransformedSecond index second third,
        binaryTransformedThird index second third] (primitiveCoordinate primitive) -
      eval ![first, second, third] (primitiveCoordinate primitive) := by
  apply mixed_coordinate_eval cocycle primitive primitive_eq pure (binaryLevel index)
    (binary_flag_fixed index) (binaryFirstCoefficient index) (binarySecondCoefficient index)
    (binaryThirdCoefficient index) (binaryFourthCoefficient index)
    (binary_first_conjugate index) (binary_second_conjugate index)
    first second third (binaryTransformedSecond index second third)
    (binaryTransformedThird index second third) (binaryScalar index) transformed_ne
  · fin_cases index
    all_goals simp [binaryFirstCoefficient, binarySecondCoefficient,
      binaryTransformedSecond, binaryTransformedThird]
    ring
  · fin_cases index
    all_goals simp [binaryThirdCoefficient, binaryFourthCoefficient,
      binaryTransformedSecond, binaryTransformedThird]
    ring
  · fin_cases index <;> norm_num [binaryFirstCoefficient, binarySecondCoefficient,
      binaryThirdCoefficient, binaryFourthCoefficient, binaryScalar]
  · intro polynomial
    exact binary_specialization index polynomial second third

end TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers
