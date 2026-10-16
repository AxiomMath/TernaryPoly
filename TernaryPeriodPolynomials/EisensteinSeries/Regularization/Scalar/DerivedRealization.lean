module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.ConjugateRotationSpan

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspScalarDerivedFunctional (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℂ where
  toFun direction := cusp.realize (cuspDerivedAction cusp direction vector) argument
  map_add' first second := by
    rw [map_add, LinearMap.add_apply, map_add, Pi.add_apply]
  map_smul' scalar direction := by
    rw [map_smul, LinearMap.smul_apply, LinearMap.map_smul_of_tower, Pi.smul_apply]
    rfl

theorem cuspScalarMatrixOrbit_fderiv_traceless (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (direction : Matrix (Fin 2) (Fin 2) ℝ) (traceless : Matrix.trace direction = 0) :
    fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) 1 direction =
      cusp.realize (cuspDerivedAction cusp direction vector) argument := by
  let difference : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℂ :=
    (fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) 1).toLinearMap -
      cuspScalarDerivedFunctional cusp vector argument
  have vanishes (matrix : BinaryRealGL) : difference (matrix.inv * binaryRotationDirection * matrix.val) = 0 := by
    change fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) 1 (matrix.inv * binaryRotationDirection * matrix.val) -
      cusp.realize (cuspDerivedAction cusp (matrix.inv * binaryRotationDirection * matrix.val) vector) argument = 0
    rw [cuspScalarMatrixOrbit_fderiv_conjugate_rotation, sub_self]
  exact sub_eq_zero.mp (binary_linear_zero_of_rotation_conjugates difference vanishes direction traceless)

theorem cusp_realize_traceless_path_hasDerivAt (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (path : ℝ → BinaryRealGL) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : path point = 1) (traceless : Matrix.trace tangent = 0)
    (derivative : ∀ row column, HasDerivAt (fun t => (path t).val row column) (tangent row column) point) :
    HasDerivAt (fun t => cusp.realize vector (argument * atInfinity (path t)))
      (cusp.realize (cuspDerivedAction cusp tangent vector) argument) point := by
  have scalar := cuspScalarMatrixOrbit_path_hasDerivAt cusp vector argument path tangent point identity derivative
  simpa only [cuspScalarMatrixOrbit_fderiv_traceless cusp vector argument tangent traceless] using scalar

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
