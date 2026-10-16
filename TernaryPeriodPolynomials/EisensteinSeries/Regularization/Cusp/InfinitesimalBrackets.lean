module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.MatrixOrbit
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspInfinitesimalAction_composition (cusp : CuspidalRepresentation)
    (first second : Matrix (Fin 2) (Fin 2) ℝ) (vector : cusp.smooth) :
    cuspInfinitesimalAction cusp (fun _ => first)
        (cuspSmoothInfinitesimalAction cusp (fun _ => second) vector) =
      fderiv ℝ (cuspMatrixOrbit cusp vector) 1 (first * second) +
        fderiv ℝ (fderiv ℝ (cuspMatrixOrbit cusp vector)) 1 first second := by
  have near : cuspMatrixOrbit cusp (cuspSmoothInfinitesimalAction cusp (fun _ => second) vector) =ᶠ[nhds 1]
      (fun matrix : Matrix (Fin 2) (Fin 2) ℝ =>
        fderiv ℝ (cuspMatrixOrbit cusp vector) matrix (matrix * second)) := by
    have domain_near : {matrix : Matrix (Fin 2) (Fin 2) ℝ | matrix.det ≠ 0} ∈ nhds 1 :=
      (isOpen_ne.preimage continuous_id.matrix_det).mem_nhds (by simp)
    filter_upwards [domain_near] with matrix invertible
    have formula := cuspMatrixOrbit_left_derivative cusp vector (invertibleMatrix matrix) second
    have value : (invertibleMatrix matrix).val = matrix := by
      simp only [invertibleMatrix, dite_eq_left invertible, GeneralLinearGroup.val_mkOfDetNeZero]
    simpa only [value, cuspMatrixOrbit, cuspSmoothInfinitesimalAction_val] using formula.symm
  have smooth := cuspMatrixOrbit_contDiffAt cusp vector 1
  have derivative_smooth : ContDiffAt ℝ ⊤ (fderiv ℝ (cuspMatrixOrbit cusp vector)) 1 :=
    smooth.fderiv_right le_top
  let right : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ second)
  have right_derivative : fderiv ℝ (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => matrix * second) 1 = right :=
    right.fderiv
  have right_differentiable : DifferentiableAt ℝ
      (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => matrix * second) 1 := right.differentiableAt
  rw [cuspInfinitesimalAction_eq_matrix_fderiv, near.fderiv_eq]
  rw [fderiv_clm_apply (derivative_smooth.differentiableAt (by simp)) right_differentiable,
    right_derivative]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, one_mul]
  rfl

theorem cuspInfinitesimalAction_commutator (cusp : CuspidalRepresentation)
    (first second : Matrix (Fin 2) (Fin 2) ℝ) (vector : cusp.smooth) :
    cuspInfinitesimalAction cusp (fun _ => first)
        (cuspSmoothInfinitesimalAction cusp (fun _ => second) vector) -
      cuspInfinitesimalAction cusp (fun _ => second)
        (cuspSmoothInfinitesimalAction cusp (fun _ => first) vector) =
      cuspInfinitesimalAction cusp (fun _ => first * second - second * first) vector := by
  rw [cuspInfinitesimalAction_composition, cuspInfinitesimalAction_composition,
    cuspInfinitesimalAction_eq_matrix_fderiv, map_sub]
  have symmetric := (cuspMatrixOrbit_contDiffAt cusp vector 1).isSymmSndFDerivAt_of_omega.eq first second
  simp only [Units.val_one] at symmetric
  rw [symmetric]
  abel

theorem cuspSmoothInfinitesimalAction_commutator (cusp : CuspidalRepresentation)
    (first second : Matrix (Fin 2) (Fin 2) ℝ) :
    cuspSmoothInfinitesimalAction cusp (fun _ => first) *
        cuspSmoothInfinitesimalAction cusp (fun _ => second) -
      cuspSmoothInfinitesimalAction cusp (fun _ => second) *
        cuspSmoothInfinitesimalAction cusp (fun _ => first) =
      cuspSmoothInfinitesimalAction cusp (fun _ => first * second - second * first) := by
  apply LinearMap.ext
  intro vector
  apply Subtype.ext
  exact cuspInfinitesimalAction_commutator cusp first second vector

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
