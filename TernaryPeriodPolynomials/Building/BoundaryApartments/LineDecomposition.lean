module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.Paths

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

variable {CoefficientRing : Type*} [CommRing CoefficientRing]

def lineBlock (matrix : Matrix (Fin 3) (Fin 3) CoefficientRing) :
    Matrix (Fin 3) (Fin 3) CoefficientRing :=
  !![matrix 0 0,0,0;0,matrix 1 1,matrix 1 2;0,matrix 2 1,matrix 2 2]

theorem lineBlock_one : lineBlock (1 : Matrix (Fin 3) (Fin 3) CoefficientRing) = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem lineBlock_mul {first second : Matrix (Fin 3) (Fin 3) CoefficientRing}
    (first_zero : first 1 0 = 0 ∧ first 2 0 = 0)
    (second_zero : second 1 0 = 0 ∧ second 2 0 = 0) :
    lineBlock (first * second) = lineBlock first * lineBlock second := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [lineBlock, Matrix.mul_apply, Fin.sum_univ_three, first_zero.1,
      first_zero.2, second_zero.1, second_zero.2, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

def lineLevi (matrix : Adelic.lineParabolic CoefficientRing) :
    GeneralLinearGroup (Fin 3) CoefficientRing where
  val := lineBlock matrix.val.val
  inv := lineBlock matrix.val.inv
  val_inv := by
    have inverse_zero := Adelic.inLine_inv matrix.property
    change lineBlock matrix.val.val * lineBlock matrix.val⁻¹.val = 1
    rw [← lineBlock_mul matrix.property inverse_zero, matrix.val.mul_inv, lineBlock_one]
  inv_val := by
    have inverse_zero := Adelic.inLine_inv matrix.property
    change lineBlock matrix.val⁻¹.val * lineBlock matrix.val.val = 1
    rw [← lineBlock_mul inverse_zero matrix.property, matrix.val.inv_mul, lineBlock_one]

theorem lineLevi_inLine (matrix : Adelic.lineParabolic CoefficientRing) :
    Adelic.InLineParabolic (lineLevi matrix) := ⟨rfl,rfl⟩

theorem lineLevi_one : lineLevi (1 : Adelic.lineParabolic CoefficientRing) = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  exact congrFun (congrFun lineBlock_one row) column

theorem lineLevi_mul (first second : Adelic.lineParabolic CoefficientRing) :
    lineLevi (first * second) = lineLevi first * lineLevi second := by
  apply GeneralLinearGroup.ext
  intro row column
  exact congrFun (congrFun (lineBlock_mul first.property second.property) row) column

def lineLeviHom : Adelic.lineParabolic CoefficientRing →*
    GeneralLinearGroup (Fin 3) CoefficientRing where
  toFun := lineLevi
  map_one' := lineLevi_one
  map_mul' := lineLevi_mul

theorem lineLevi_inv (matrix : Adelic.lineParabolic CoefficientRing) :
    lineLevi matrix⁻¹ = (lineLevi matrix)⁻¹ :=
  map_inv lineLeviHom matrix

def lineRadical (matrix : Adelic.lineParabolic CoefficientRing) :
    GeneralLinearGroup (Fin 3) CoefficientRing := matrix.val * (lineLevi matrix)⁻¹

theorem lineRadical_times_levi (matrix : Adelic.lineParabolic CoefficientRing) :
    lineRadical matrix * lineLevi matrix = matrix.val := by
  simp [lineRadical]

theorem lineLevi_map {TargetRing : Type*} [CommRing TargetRing]
    (ringMap : CoefficientRing →+* TargetRing)
    (matrix : Adelic.lineParabolic CoefficientRing) :
    lineLevi ⟨GeneralLinearGroup.map ringMap matrix.val,
      Adelic.inLine_map ringMap matrix.val matrix.property⟩ =
        GeneralLinearGroup.map ringMap (lineLevi matrix) := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [lineLevi, lineBlock, GeneralLinearGroup.map_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

theorem lineRadical_upper (matrix : Adelic.lineParabolic CoefficientRing) :
    lineRadical matrix = Adelic.lineUnipotent
      ((lineRadical matrix).val 0 1) ((lineRadical matrix).val 0 2) := by
  have inverse_eq := lineLevi_inv matrix
  have inverse_zero := Adelic.inLine_inv matrix.property
  have inverse_matrix_zero : (matrix.val.val)⁻¹ 1 0 = 0 ∧ (matrix.val.val)⁻¹ 2 0 = 0 := by
    simpa only [Adelic.InLineParabolic, GeneralLinearGroup.coe_inv] using inverse_zero
  have diagonal_eq := congrArg (fun entry : GeneralLinearGroup (Fin 3) CoefficientRing =>
    entry.val) inverse_eq
  have inverse_entries : ((lineLevi matrix)⁻¹).val = lineBlock matrix.val.inv :=
    diagonal_eq.symm
  apply GeneralLinearGroup.ext
  intro row column
  have coordinate := congrArg (fun entry : Matrix (Fin 3) (Fin 3) CoefficientRing =>
    entry row column) matrix.val.mul_inv
  fin_cases row <;> fin_cases column <;>
    simp only [Adelic.lineUnipotent, Adelic.upperUnipotent] <;>
    first
    | rfl
    | (simp [lineRadical, inverse_entries, lineBlock,
          Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
          matrix.property.1, matrix.property.2];
       all_goals simpa [Matrix.mul_apply, Fin.sum_univ_three, matrix.property.1,
         matrix.property.2, inverse_matrix_zero.1, inverse_matrix_zero.2] using coordinate)

theorem lineLevi_arithmetic {matrix : IntegralGL3}
    (matrix_arithmetic : matrix ∈ arithmeticLevel)
    (matrix_line : matrix ∈ Adelic.lineParabolic ℤ) :
    lineLevi ⟨matrix, matrix_line⟩ ∈ arithmeticLevel := by
  have entry := arithmetic_lastRow (⟨matrix, matrix_arithmetic⟩ : arithmeticLevel)
  change lastRow ᵥ* (reductionThree (lineLevi ⟨matrix, matrix_line⟩)).val = lastRow
  simp only [lastRow, Matrix.single_vecMul, one_smul]
  ext index
  fin_cases index
  · rfl
  · change (matrix.val 2 1 : ZMod 3) = 0
    exact entry 1
  · change (matrix.val 2 2 : ZMod 3) = 1
    exact entry 2

theorem rational_lineLevi_mem (matrix : rationalLevel)
    (matrix_line : matrix.val ∈ Adelic.lineParabolic ℚ) :
    lineLevi ⟨matrix.val, matrix_line⟩ ∈ rationalLevel := by
  rcases matrix.property with ⟨integral, integral_eq⟩
  have integral_line : integral.val ∈ Adelic.lineParabolic ℤ := by
    constructor
    · have coordinate := matrix_line.1
      rw [← integral_eq] at coordinate
      change (integral.val.val 1 0 : ℚ) = 0 at coordinate
      exact_mod_cast coordinate
    · have coordinate := matrix_line.2
      rw [← integral_eq] at coordinate
      change (integral.val.val 2 0 : ℚ) = 0 at coordinate
      exact_mod_cast coordinate
  let integral_levi : arithmeticLevel :=
    ⟨lineLevi ⟨integral.val, integral_line⟩, lineLevi_arithmetic integral.property integral_line⟩
  refine ⟨integral_levi, ?_⟩
  change GeneralLinearGroup.map (Int.castRingHom ℚ) (lineLevi ⟨integral.val, integral_line⟩) = _
  rw [← lineLevi_map]
  apply GeneralLinearGroup.ext
  intro row column
  have matrix_eq : GeneralLinearGroup.map (Int.castRingHom ℚ) integral.val = matrix.val := integral_eq
  simp only [matrix_eq]

def badLineSubgroup : Subgroup RationalGL3 := rationalLevel ⊓ Adelic.lineParabolic ℚ

def arithmeticLevi (matrix : badLineSubgroup) : rationalLevel :=
  ⟨lineLevi ⟨matrix.val, matrix.property.2⟩,
    rational_lineLevi_mem ⟨matrix.val, matrix.property.1⟩ matrix.property.2⟩

def arithmeticRadical (matrix : badLineSubgroup) : rationalLevel :=
  (⟨matrix.val, matrix.property.1⟩ : rationalLevel) * (arithmeticLevi matrix)⁻¹

theorem arithmeticRadical_val (matrix : badLineSubgroup) :
    (arithmeticRadical matrix).val = lineRadical ⟨matrix.val, matrix.property.2⟩ := rfl

theorem arithmeticRadical_mul_levi (matrix : badLineSubgroup) :
    arithmeticRadical matrix * arithmeticLevi matrix =
      (⟨matrix.val, matrix.property.1⟩ : rationalLevel) := by
  simp [arithmeticRadical]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
