module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.RelativeRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLeviAnalyticAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryInvertibleMatrix_inverse_val_contDiffAt_one :
    ContDiffAt ℝ ⊤ (fun matrix : BinaryRealMatrix => (invertibleMatrix matrix)⁻¹.val) 1 := by
  have domain_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  apply contDiffAt_pi.mpr
  intro row
  apply contDiffAt_pi.mpr
  intro column
  have regular := binary_matrix_inv_contDiffOn (fun matrix : BinaryRealMatrix => matrix)
    (fun row column => by fun_prop) (domain := {matrix : BinaryRealMatrix | matrix.det ≠ 0})
    (fun _ member => member) row column (order := ⊤)
  have lifted : ContDiffOn ℝ ⊤ (fun matrix : BinaryRealMatrix => (invertibleMatrix matrix)⁻¹.val row column)
      {matrix : BinaryRealMatrix | matrix.det ≠ 0} := by
    apply regular.congr
    intro matrix member
    rw [GeneralLinearGroup.coe_inv, invertibleMatrix_val matrix member]
  exact lifted.contDiffAt (domain_open.mem_nhds (show (1 : BinaryRealMatrix).det ≠ 0 by simp))

theorem realRadicalInverseLevi_matrix_contDiffAt_one (radical : RealPlaneRadical) :
    ContDiffAt ℝ ⊤ (fun matrix : BinaryRealMatrix =>
      (realRadicalInverseLevi (invertibleMatrix matrix) radical).toAdd) 1 := by
  change ContDiffAt ℝ ⊤ (fun matrix : BinaryRealMatrix => (invertibleMatrix matrix)⁻¹.val.mulVec radical.toAdd) 1
  apply contDiffAt_pi.mpr
  intro row
  change ContDiffAt ℝ ⊤ (fun matrix : BinaryRealMatrix => ∑ column,
    (invertibleMatrix matrix)⁻¹.val row column * radical.toAdd column) 1
  apply ContDiffAt.sum
  intro column _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp binaryInvertibleMatrix_inverse_val_contDiffAt_one row) column).mul contDiffAt_const

theorem realPlaneLeviMatrix_contDiffAt_one :
    ContDiffAt ℝ ⊤ (fun matrix : BinaryRealMatrix =>
      (realPlaneMatrix (SemidirectProduct.inr (invertibleMatrix matrix))).val) 1 := by
  simp only [realPlaneMatrix_inr]
  exact planeBlockOne_contDiff.contDiffAt.comp 1 binaryInvertibleMatrix_val_contDiffAt_one

theorem realPlaneInverseRadicalMatrix_contDiffAt_one (radical : RealPlaneRadical) :
    ContDiffAt ℝ ⊤ (fun matrix : BinaryRealMatrix =>
      (realPlaneMatrix (SemidirectProduct.inl (realRadicalInverseLevi (invertibleMatrix matrix) radical))).val) 1 := by
  simp only [realPlaneMatrix_inl]
  convert realPlaneRadicalMatrix_contDiff.contDiffAt.comp
    (f := fun matrix : BinaryRealMatrix => (realRadicalInverseLevi (invertibleMatrix matrix) radical).toAdd)
    1 (realRadicalInverseLevi_matrix_contDiffAt_one radical) using 1
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
