module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.MatrixDifferential

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryHorizontalGenerator : BinaryRealMatrix := !![0, 1; 0, 0]

def binaryDiagonalGenerator : BinaryRealMatrix := !![1/2, 0; 0, -1/2]

def binaryRotationGenerator : BinaryRealMatrix := !![0, -1; 1, 0]

def binarySymmetricGenerator : BinaryRealMatrix := !![0, 1/2; 1/2, 0]

theorem binarySymmetricGenerator_decomposition :
    binarySymmetricGenerator = binaryHorizontalGenerator + (1/2 : ℝ) • binaryRotationGenerator := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [binarySymmetricGenerator, binaryHorizontalGenerator, binaryRotationGenerator]

theorem binarySymmetricGenerator_conjugation (angle : Circle) :
    (binaryRotations angle)⁻¹.val * binarySymmetricGenerator * (binaryRotations angle).val =
      ((angle : ℂ).re ^ 2 - (angle : ℂ).im ^ 2) • binarySymmetricGenerator +
        (2 * (angle : ℂ).re * (angle : ℂ).im) • binaryDiagonalGenerator := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryRotations, binaryRotation, binarySymmetricGenerator, binaryDiagonalGenerator,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem binaryDiagonalGenerator_conjugation (angle : Circle) :
    (binaryRotations angle)⁻¹.val * binaryDiagonalGenerator * (binaryRotations angle).val =
      ((angle : ℂ).re ^ 2 - (angle : ℂ).im ^ 2) • binaryDiagonalGenerator -
        (2 * (angle : ℂ).re * (angle : ℂ).im) • binarySymmetricGenerator := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryRotations, binaryRotation, binarySymmetricGenerator, binaryDiagonalGenerator,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem binaryRotation_inverse_square (angle : Circle) :
    (angle : ℂ) ^ (-2 : ℤ) =
      (((angle : ℂ).re ^ 2 - (angle : ℂ).im ^ 2 : ℝ) : ℂ) -
        Complex.I * ((2 * (angle : ℂ).re * (angle : ℂ).im : ℝ) : ℂ) := by
  have inverse : (angle : ℂ) ^ (-2 : ℤ) = ((starRingEnd ℂ) (angle : ℂ)) ^ 2 := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow, ← Circle.coe_inv, Circle.coe_inv_eq_conj]
  rw [inverse]
  apply Complex.ext <;> simp [pow_two]
  ring

def cuspFullRaisingVector (cusp : CuspidalRepresentation) (vector : cusp.H) : cusp.H :=
  cuspMatrixDifferential cusp vector binarySymmetricGenerator +
    Complex.I • cuspMatrixDifferential cusp vector binaryDiagonalGenerator

def cuspFullLoweringVector (cusp : CuspidalRepresentation) (vector : cusp.H) : cusp.H :=
  cuspMatrixDifferential cusp vector binarySymmetricGenerator -
    Complex.I • cuspMatrixDifferential cusp vector binaryDiagonalGenerator

theorem cuspFullRaisingVector_rotation (cusp : CuspidalRepresentation) (vector : cusp.smooth) (angle : Circle) :
    cuspFullRaisingVector cusp (cusp.π (atInfinity (binaryRotations angle)) vector.val) =
      (angle : ℂ) ^ (-2 : ℤ) • cusp.π (atInfinity (binaryRotations angle)) (cuspFullRaisingVector cusp vector.val) := by
  simp only [cuspFullRaisingVector, cuspMatrixDifferential_translate cusp vector,
    binarySymmetricGenerator_conjugation, binaryDiagonalGenerator_conjugation,
    map_add, map_sub, map_smul, binaryRotation_inverse_square,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have scalar (first second : ℂ) : (first - Complex.I * second) * Complex.I = second + Complex.I * first := by
    calc
      _ = Complex.I * first - (Complex.I * Complex.I) * second := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  simp only [smul_add, smul_sub, smul_smul, scalar]
  module

end TernaryPeriodPolynomials.SphericalDetection.Helpers
