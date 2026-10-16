module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.FlatSectionWeight
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.ArchimedeanIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlaneRowSquare (matrix : RealGL3) : ℝ :=
  ∑ index : Fin 3, (matrix.val 2 index) ^ 2

theorem realPlaneRowSquare_pos (matrix : RealGL3) : 0 < realPlaneRowSquare matrix := by
  have nonnegative : 0 ≤ realPlaneRowSquare matrix := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_contra failure
  have zero : realPlaneRowSquare matrix = 0 := le_antisymm (le_of_not_gt failure) nonnegative
  have entries (index : Fin 3) : matrix.val 2 index = 0 := by
    have square : (matrix.val 2 index) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp zero index (Finset.mem_univ _)
    exact sq_eq_zero_iff.mp square
  have inverse := congrArg (fun value : Matrix (Fin 3) (Fin 3) ℝ => value 2 2) matrix.mul_inv
  simp only [Matrix.mul_apply, entries, zero_mul, Finset.sum_const_zero, Matrix.one_apply_eq] at inverse
  exact zero_ne_one inverse

def realPlaneFlatWeight (parameter : ℂ) (matrix : RealGL3) : ℂ :=
  Complex.exp (inductionExponent .plane parameter *
    ((Real.log matrix.val.det : ℂ) - (3 / 2 : ℂ) * (Real.log (realPlaneRowSquare matrix) : ℂ)))

theorem realPlaneFlatWeight_ne_zero (parameter : ℂ) (matrix : RealGL3) :
    realPlaneFlatWeight parameter matrix ≠ 0 := Complex.exp_ne_zero _

theorem realPlaneFlatWeight_endpoint (matrix : RealGL3) :
    realPlaneFlatWeight cohomologicalPoint matrix = 1 := by
  have exponent : inductionExponent .plane cohomologicalPoint = 0 := by
    unfold inductionExponent cohomologicalPoint
    ring
  simp [realPlaneFlatWeight, exponent]

theorem realOrthogonal_det_log (compact : RealGL3)
    (orthogonal : compact.val.transpose * compact.val = 1) : Real.log compact.val.det = 0 := by
  have determinant := congrArg Matrix.det orthogonal
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← pow_two] at determinant
  have logarithm := congrArg Real.log determinant
  rw [Real.log_pow, Real.log_one] at logarithm
  simp only [Nat.cast_ofNat] at logarithm
  linarith

theorem realPlaneInduction_row (first second : ℝ) (scalar : ℝˣ) (block : BinaryRealGL)
    (compact : RealGL3) (index : Fin 3) :
    (planeUnipotent first second * (planeLevi 1 scalar * (planeLevi block 1 * compact))).val 2 index =
      scalar.val * compact.val 2 index := by
  simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem realPlaneInduction_rowSquare (first second : ℝ) (scalar : ℝˣ) (block : BinaryRealGL)
    (compact : RealGL3) (orthogonal : compact.val.transpose * compact.val = 1) :
    realPlaneRowSquare (planeUnipotent first second * (planeLevi 1 scalar * (planeLevi block 1 * compact))) =
      scalar.val ^ 2 := by
  have reverse : compact.val * compact.val.transpose = 1 := mul_eq_one_comm.mp orthogonal
  have row := congrArg (fun value : Matrix (Fin 3) (Fin 3) ℝ => value 2 2) reverse
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, ← pow_two] at row
  simp only [realPlaneRowSquare, realPlaneInduction_row, mul_pow, ← Finset.mul_sum, row, mul_one]

theorem realPlaneInduction_det (first second : ℝ) (scalar : ℝˣ) (block : BinaryRealGL)
    (compact : RealGL3) :
    (planeUnipotent first second * (planeLevi 1 scalar * (planeLevi block 1 * compact))).val.det =
      block.val.det * scalar.val * compact.val.det := by
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]
  have radical : (planeUnipotent first second).val.det = 1 := by
    simp [planeUnipotent, Matrix.det_fin_three]
  have scalar_det : (planeLevi 1 scalar).val.det = scalar.val := by
    simp [planeLevi, planeBlock, Matrix.det_fin_three]
  have block_det : (planeLevi block 1).val.det = block.val.det := by
    simp [planeLevi, planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  rw [radical, scalar_det, block_det, one_mul]
  ring

theorem realPlaneFlatWeight_inductionCoordinates (parameter : ℂ)
    (first second : ℝ) (scalar : ℝˣ) (block : BinaryRealGL)
    (compact : RealGL3) (orthogonal : compact.val.transpose * compact.val = 1) :
    realPlaneFlatWeight parameter
        (planeUnipotent first second * (planeLevi 1 scalar * (planeLevi block 1 * compact))) =
      normPower (realAdeleUnit (GeneralLinearGroup.det block)) (inductionExponent .plane parameter) *
        normPower (realAdeleUnit scalar) (-2 * inductionExponent .plane parameter) := by
  have block_nonzero : block.val.det ≠ 0 := (GeneralLinearGroup.det block).ne_zero
  have compact_nonzero : compact.val.det ≠ 0 := (GeneralLinearGroup.det compact).ne_zero
  rw [realPlaneFlatWeight, realPlaneInduction_det, realPlaneInduction_rowSquare _ _ _ _ _ orthogonal,
    Real.log_mul (mul_ne_zero block_nonzero scalar.ne_zero) compact_nonzero,
    Real.log_mul block_nonzero scalar.ne_zero, realOrthogonal_det_log compact orthogonal, add_zero,
    Real.log_pow]
  simp only [normPower, adeleNorm_realAdeleUnit, GeneralLinearGroup.val_det_apply,
    Real.log_abs, Complex.ofReal_add, Complex.ofReal_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem standardGoodLineRealArgument_val (real : ℝ × ℝ) :
    (standardGoodLineRealArgument real).val = !![0,1,0;1,0,0;real.2,real.1,1] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [standardGoodLineRealArgument, weyl, lineUnipotent, upperUnipotent, rationalGoodLine,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem standardGoodLineRealArgument_rowSquare (real : ℝ × ℝ) :
    realPlaneRowSquare (standardGoodLineRealArgument real) = 1 + real.1 ^ 2 + real.2 ^ 2 := by
  simp only [realPlaneRowSquare, standardGoodLineRealArgument_val, Fin.sum_univ_three]
  change real.2 ^ 2 + real.1 ^ 2 + 1 ^ 2 = _
  ring

theorem standardGoodLineRealArgument_det (real : ℝ × ℝ) :
    (standardGoodLineRealArgument real).val.det = -1 := by
  rw [standardGoodLineRealArgument_val, Matrix.det_fin_three]
  simp

theorem realPlaneFlatWeight_standardGoodLine (parameter : ℂ) (real : ℝ × ℝ) :
    realPlaneFlatWeight parameter (standardGoodLineRealArgument real) =
      Complex.exp ((-(3 : ℂ) / 4 - parameter / 2) * (Real.log (1 + real.1 ^ 2 + real.2 ^ 2) : ℂ)) := by
  rw [realPlaneFlatWeight, standardGoodLineRealArgument_det, standardGoodLineRealArgument_rowSquare]
  simp only [Real.log_neg_eq_log, Real.log_one, Complex.ofReal_zero, zero_sub]
  congr 1
  unfold inductionExponent
  ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
