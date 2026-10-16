module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.DerivedLieAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspSmoothAction (cusp : CuspidalRepresentation) :
    Representation ℂ BinaryAdelicGL cusp.smooth where
  toFun matrix :=
    { toFun := fun vector => ⟨cusp.π matrix vector.val, cusp.smooth_stable _ _ vector.property⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  map_one' := by
    apply LinearMap.ext
    intro vector
    apply Subtype.ext
    exact congrArg (fun action => action vector.val) cusp.π.map_one
  map_mul' first second := by
    apply LinearMap.ext
    intro vector
    apply Subtype.ext
    exact congrArg (fun action => action vector.val) (cusp.π.map_mul first second)

theorem cuspSmoothAction_apply_val (cusp : CuspidalRepresentation)
    (matrix : BinaryAdelicGL) (vector : cusp.smooth) :
    (cuspSmoothAction cusp matrix vector).val = cusp.π matrix vector.val := rfl

theorem cuspMatrixOrbit_right_mul (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (matrix : BinaryRealGL) {entries : Matrix (Fin 2) (Fin 2) ℝ} (invertible : entries.det ≠ 0) :
    cuspMatrixOrbit cusp (cuspSmoothAction cusp (atInfinity matrix) vector) entries =
      cuspMatrixOrbit cusp vector (entries * matrix.val) := by
  have value : entries * matrix.val = (invertibleMatrix entries * matrix).val := by
    simp only [Units.val_mul, invertibleMatrix, dite_eq_left invertible, GeneralLinearGroup.val_mkOfDetNeZero]
  simp only [cuspMatrixOrbit, cuspSmoothAction_apply_val, value, invertibleMatrix_val,
    binary_atInfinity_mul, map_mul, Module.End.mul_apply]

theorem cuspDerivedAction_real_covariance (cusp : CuspidalRepresentation)
    (matrix : BinaryRealGL) (direction : Matrix (Fin 2) (Fin 2) ℝ) (vector : cusp.smooth) :
    cuspDerivedAction cusp direction (cuspSmoothAction cusp (atInfinity matrix) vector) =
      cuspSmoothAction cusp (atInfinity matrix)
        (cuspDerivedAction cusp (matrix.inv * direction * matrix.val) vector) := by
  apply Subtype.ext
  rw [cuspDerivedAction_apply_val, cuspSmoothAction_apply_val]
  let right : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ matrix.val)
  have differentiable : DifferentiableAt ℝ (cuspMatrixOrbit cusp vector) (right 1) := by
    change DifferentiableAt ℝ (cuspMatrixOrbit cusp vector) (1 * matrix.val)
    rw [one_mul]
    exact (cuspMatrixOrbit_contDiffAt cusp vector matrix).differentiableAt (by simp)
  have differentiated := differentiable.hasFDerivAt.comp 1 right.hasFDerivAt
  have applied := congrArg (fun linear => linear direction) differentiated.fderiv
  have near : cuspMatrixOrbit cusp (cuspSmoothAction cusp (atInfinity matrix) vector) =ᶠ[nhds 1]
      (fun entries => cuspMatrixOrbit cusp vector (entries * matrix.val)) := by
    have domain_near : ∀ᶠ entries : Matrix (Fin 2) (Fin 2) ℝ in nhds 1, entries.det ≠ 0 :=
      (isOpen_ne.preimage continuous_id.matrix_det).eventually_mem (by simp)
    filter_upwards [domain_near] with entries invertible
    exact cuspMatrixOrbit_right_mul cusp vector matrix invertible
  rw [near.fderiv_eq]
  change fderiv ℝ (fun entries => cuspMatrixOrbit cusp vector (entries * matrix.val)) 1 direction = _
  change fderiv ℝ (fun entries => cuspMatrixOrbit cusp vector (entries * matrix.val)) 1 direction =
    fderiv ℝ (cuspMatrixOrbit cusp vector) (1 * matrix.val) (direction * matrix.val) at applied
  rw [one_mul] at applied
  rw [applied]
  have tangent : direction * matrix.val = matrix.val * (matrix.inv * direction * matrix.val) := by
    rw [← mul_assoc, ← mul_assoc, matrix.val_inv, one_mul]
  rw [tangent, cuspMatrixOrbit_left_derivative]
  rfl

theorem cuspDerivedAction_finite_covariance (cusp : CuspidalRepresentation)
    (matrix : BinaryFiniteGL) (direction : Matrix (Fin 2) (Fin 2) ℝ) (vector : cusp.smooth) :
    cuspDerivedAction cusp direction (cuspSmoothAction cusp (atFinite matrix) vector) =
      cuspSmoothAction cusp (atFinite matrix) (cuspDerivedAction cusp direction vector) := by
  apply Subtype.ext
  have derivative := congrArg (fun form => form (fun _ => fun _ => direction))
    (cuspOrbitDerivative_finite_translate cusp 1 vector matrix)
  exact derivative

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
