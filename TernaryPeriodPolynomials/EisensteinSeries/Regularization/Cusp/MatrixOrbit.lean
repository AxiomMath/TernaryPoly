module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.DifferentiatedVectors

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspMatrixOrbit (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) : cusp.H :=
  cusp.π (atInfinity (invertibleMatrix matrix)) vector.val

theorem cuspMatrixOrbit_contDiffOn (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    ContDiffOn ℝ ⊤ (cuspMatrixOrbit cusp vector) {matrix | matrix.det ≠ 0} := by
  have smooth := ((cusp.smooth_exact vector.val).mp vector.property).1
  have tuples_smooth : ContDiff ℝ ⊤
      (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => fun _ : Fin 1 => matrix) :=
    contDiff_pi.mpr (fun _ => contDiff_id)
  have composed := smooth.comp tuples_smooth.contDiffOn (fun _ member _ => member)
  exact composed

theorem cuspMatrixOrbit_contDiffAt (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (matrix : BinaryRealGL) : ContDiffAt ℝ ⊤ (cuspMatrixOrbit cusp vector) matrix.val := by
  apply (cuspMatrixOrbit_contDiffOn cusp vector).contDiffAt
  exact (isOpen_ne.preimage continuous_id.matrix_det).mem_nhds matrix.det_ne_zero

theorem cuspInfinitesimalAction_eq_matrix_fderiv (cusp : CuspidalRepresentation)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) (vector : cusp.smooth) :
    cuspInfinitesimalAction cusp direction vector =
      fderiv ℝ (cuspMatrixOrbit cusp vector) 1 (direction 0) := by
  have smooth := cuspMatrixOrbit_contDiffAt cusp vector 1
  have differentiated := (smooth.differentiableAt (by simp)).hasFDerivAt.comp
    (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix (Fin 2) (Fin 2) ℝ) 0).hasFDerivAt
  have applied := congrArg (fun linear => linear direction) differentiated.fderiv
  change fderiv ℝ (fun entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      cuspMatrixOrbit cusp vector (entries 0)) (fun _ => 1) direction =
    fderiv ℝ (cuspMatrixOrbit cusp vector) 1 (direction 0) at applied
  simpa only [cuspInfinitesimalAction, cuspOrbitDerivative, LinearMap.coe_mk, AddHom.coe_mk,
    iteratedFDeriv_one_apply, cuspMatrixOrbit] using applied

theorem cuspMatrixOrbit_mul (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (first : BinaryRealGL) {second : Matrix (Fin 2) (Fin 2) ℝ} (invertible : second.det ≠ 0) :
    cuspMatrixOrbit cusp vector (first.val * second) =
      cusp.π (atInfinity first) (cuspMatrixOrbit cusp vector second) := by
  have value : first.val * second = (first * invertibleMatrix second).val := by
    simp only [Units.val_mul, invertibleMatrix, dite_eq_left invertible, GeneralLinearGroup.val_mkOfDetNeZero]
  simp only [cuspMatrixOrbit, value, invertibleMatrix_val, binary_atInfinity_mul,
    map_mul, Module.End.mul_apply]

theorem cuspMatrixOrbit_left_derivative (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (matrix : BinaryRealGL) (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    fderiv ℝ (cuspMatrixOrbit cusp vector) matrix.val (matrix.val * direction) =
      cusp.π (atInfinity matrix)
        (cuspInfinitesimalAction cusp (fun _ => direction) vector) := by
  let left : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ matrix.val)
  let projection : (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    ContinuousLinearMap.proj 0
  have smooth := cuspMatrixOrbit_contDiffAt cusp vector matrix
  have at_image : DifferentiableAt ℝ (cuspMatrixOrbit cusp vector)
      ((left.comp projection) (fun _ => 1)) := by
    change DifferentiableAt ℝ (cuspMatrixOrbit cusp vector) (matrix.val * 1)
    rw [mul_one]
    exact smooth.differentiableAt (by simp)
  have differentiated := at_image.hasFDerivAt.comp (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (left.comp projection).hasFDerivAt
  have applied := congrArg (fun linear => linear (fun _ => direction)) differentiated.fderiv
  change fderiv ℝ (fun entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      cuspMatrixOrbit cusp vector (matrix.val * entries 0)) (fun _ => 1) (fun _ => direction) =
    fderiv ℝ (cuspMatrixOrbit cusp vector) (matrix.val * 1) (matrix.val * direction) at applied
  rw [mul_one] at applied
  have near : (fun entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      cuspMatrixOrbit cusp vector (matrix.val * entries 0)) =ᶠ[nhds (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ))]
      (fun entries => cusp.π (atInfinity matrix) (cuspMatrixOrbit cusp vector (entries 0))) := by
    have domain_near := (invertibleMatrixTuples_isOpen 2 1).mem_nhds
      (show (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∈
        {entries | ∀ index, (entries index).det ≠ 0} from fun _ => by simp)
    filter_upwards [domain_near] with entries member
    exact cuspMatrixOrbit_mul cusp vector matrix (member 0)
  rw [near.fderiv_eq] at applied
  rw [← applied]
  exact cuspInfinitesimalAction_left_translate_fderiv cusp (fun _ => direction) vector matrix

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
