module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CoefficientDerivedOperator

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspSmoothAction_path_hasDerivAt
    (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (path : ℝ → BinaryRealGL) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : path point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => (path t).val row column) (tangent row column) point) :
    HasDerivAt (fun t => (cuspSmoothAction cusp (atInfinity (path t)) vector).val)
      (cuspDerivedAction cusp tangent vector).val point := by
  have matrix_derivative : HasDerivAt (fun t => (path t).val) tangent point :=
    hasDerivAt_pi.mpr (fun row => hasDerivAt_pi.mpr (derivative row))
  have orbit_derivative := ((cuspMatrixOrbit_contDiffAt cusp vector 1).differentiableAt (by simp)).hasFDerivAt
  have computed := orbit_derivative.comp_hasDerivAt_of_eq point matrix_derivative (by simp [identity])
  convert! computed using 1
  · ext t
    simp [cuspSmoothAction_apply_val, cuspMatrixOrbit, invertibleMatrix_val]
  · exact cuspDerivedAction_apply_val cusp tangent vector

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
