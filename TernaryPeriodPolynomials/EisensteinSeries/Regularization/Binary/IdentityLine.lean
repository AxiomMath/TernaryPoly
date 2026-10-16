module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.PathDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def binaryIdentityLine (direction : Matrix (Fin 2) (Fin 2) ℝ) (parameter : ℝ) : BinaryRealGL :=
  invertibleMatrix (1 + parameter • direction)

theorem binaryIdentityLine_zero (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryIdentityLine direction 0 = 1 := by
  simp only [binaryIdentityLine, zero_smul, add_zero]
  exact invertibleMatrix_val 1

theorem binaryIdentityLine_val_eventuallyEq (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    (fun parameter => (binaryIdentityLine direction parameter).val) =ᶠ[nhds 0]
      (fun parameter => 1 + parameter • direction) := by
  have continuous : Continuous (fun parameter : ℝ => (1 + parameter • direction).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have near : ∀ᶠ parameter : ℝ in nhds 0, (1 + parameter • direction).det ≠ 0 :=
    continuous.continuousAt.eventually_ne (by simp)
  filter_upwards [near] with parameter invertible
  simp only [binaryIdentityLine, invertibleMatrix, dite_eq_left invertible, GeneralLinearGroup.val_mkOfDetNeZero]

theorem binaryIdentityLine_hasDerivAt (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    HasDerivAt (fun parameter => (binaryIdentityLine direction parameter).val) direction 0 := by
  have line : HasDerivAt (fun parameter : ℝ => 1 + parameter • direction) direction 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add (1 : Matrix (Fin 2) (Fin 2) ℝ) using 1
    simp
  exact line.congr_of_eventuallyEq (binaryIdentityLine_val_eventuallyEq direction)

theorem binaryIdentityLine_entry_hasDerivAt (direction : Matrix (Fin 2) (Fin 2) ℝ)
    (row column : Fin 2) :
    HasDerivAt (fun parameter => (binaryIdentityLine direction parameter).val row column) (direction row column) 0 :=
  hasDerivAt_pi.mp (hasDerivAt_pi.mp (binaryIdentityLine_hasDerivAt direction) row) column

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
