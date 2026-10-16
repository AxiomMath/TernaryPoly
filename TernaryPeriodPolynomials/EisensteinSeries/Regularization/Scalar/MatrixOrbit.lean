module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.RotationDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspScalarMatrixOrbit (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (matrix : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  cusp.realize vector (argument * atInfinity (invertibleMatrix matrix))

theorem cuspScalarMatrixOrbit_contDiffOn (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) :
    ContDiffOn ℝ ⊤ (cuspScalarMatrixOrbit cusp vector argument) {matrix | matrix.det ≠ 0} := by
  have tuples : ContDiff ℝ ⊤ (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => fun _ : Fin 1 => matrix) :=
    contDiff_pi.mpr (fun _ => contDiff_id)
  have composed := (cusp.scalarSmooth vector argument).comp tuples.contDiffOn (fun _ member _ => member)
  convert! composed using 1

theorem cuspScalarMatrixOrbit_contDiffAt (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (matrix : BinaryRealGL) :
    ContDiffAt ℝ ⊤ (cuspScalarMatrixOrbit cusp vector argument) matrix.val := by
  apply (cuspScalarMatrixOrbit_contDiffOn cusp vector argument).contDiffAt
  exact (isOpen_ne.preimage continuous_id.matrix_det).mem_nhds matrix.det_ne_zero

theorem cuspScalarMatrixOrbit_path_hasDerivAt (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (path : ℝ → BinaryRealGL) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : path point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => (path t).val row column) (tangent row column) point) :
    HasDerivAt (fun t => cusp.realize vector (argument * atInfinity (path t)))
      (fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) 1 tangent) point := by
  have matrix_derivative : HasDerivAt (fun t => (path t).val) tangent point :=
    hasDerivAt_pi.mpr (fun row => hasDerivAt_pi.mpr (derivative row))
  have orbit_derivative := ((cuspScalarMatrixOrbit_contDiffAt cusp vector argument 1).differentiableAt (by simp)).hasFDerivAt
  have computed := orbit_derivative.comp_hasDerivAt_of_eq point matrix_derivative (by simp [identity])
  convert! computed using 1
  funext t
  simp only [Function.comp_def, cuspScalarMatrixOrbit, invertibleMatrix_val]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
