/-
  `invertibleMatrix` is compatible with matrix multiplication and conjugation on
  the invertible locus.  These are the group-element identities behind the
  multi-variable smoothness transport of `HasSmoothCuspLift`.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothTransport

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.MatrixConjLemmas

theorem invertibleMatrix_mul {C A : Matrix (Fin 3) (Fin 3) ℝ}
    (hC : C.det ≠ 0) (hA : A.det ≠ 0) :
    invertibleMatrix (C * A) = invertibleMatrix C * invertibleMatrix A := by
  apply Units.ext
  rw [SmoothTransport.invertibleMatrix_val (A := C * A) (by rw [Matrix.det_mul]; exact mul_ne_zero hC hA),
    Units.val_mul, SmoothTransport.invertibleMatrix_val (A := C) hC,
    SmoothTransport.invertibleMatrix_val (A := A) hA]

/-- Conjugation by an invertible matrix corresponds to group conjugation by
`invertibleMatrix C`. -/
theorem invertibleMatrix_mul_conj {C A : Matrix (Fin 3) (Fin 3) ℝ}
    (hC : C.det ≠ 0) (hA : A.det ≠ 0) :
    invertibleMatrix (C * A * (C⁻¹)) =
      invertibleMatrix C * invertibleMatrix A * (invertibleMatrix C)⁻¹ := by
  have hCi : (C⁻¹).det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det C (isUnit_iff_ne_zero.mpr hC)).ne_zero
  apply Units.ext
  rw [SmoothTransport.invertibleMatrix_val (A := C * A * C⁻¹)
        (by rw [Matrix.det_mul, Matrix.det_mul]; exact mul_ne_zero (mul_ne_zero hC hA) hCi),
    Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_inv,
    SmoothTransport.invertibleMatrix_val (A := C) hC,
    SmoothTransport.invertibleMatrix_val (A := A) hA]

end TernaryPeriodPolynomials.HeckeTranslate.MatrixConjLemmas

end
