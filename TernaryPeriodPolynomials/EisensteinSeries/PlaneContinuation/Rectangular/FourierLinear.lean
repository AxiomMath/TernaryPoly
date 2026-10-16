module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Theta.DistortionPoisson
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFourierLinear

theorem lattice_rank : Module.finrank ℤ integerLattice = 6 := by
  rw [ZLattice.rank ℝ integerLattice]
  simp [RealSpace, Coordinate]

theorem basis_matrix_entry (source : Coordinate) (row : Fin 3) (column : Fin 2) :
    coordinateEquiv.symm ((EuclideanSpace.basisFun Coordinate ℝ) source) row column =
      if (row, column) = source then 1 else 0 := by
  change ((EuclideanSpace.basisFun Coordinate ℝ) source) (row, column) = _
  rw [EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem transformation_matrix (point : GeneralLinearGroup (Fin 3) ℝ) (binary : GeneralLinearGroup (Fin 2) ℝ) :
    LinearMap.toMatrix (EuclideanSpace.basisFun Coordinate ℝ).toBasis (EuclideanSpace.basisFun Coordinate ℝ).toBasis
      (realTransform point binary).toLinearEquiv.toLinearMap =
        Matrix.kroneckerMap (fun first second => first * second) point⁻¹.val binary.val.transpose := by
  ext ⟨row, column⟩ ⟨sourceRow, sourceColumn⟩
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    Matrix.kroneckerMap_apply]
  change (point⁻¹.val * coordinateEquiv.symm ((EuclideanSpace.basisFun Coordinate ℝ) (sourceRow, sourceColumn)) *
    binary.val) row column =
    point⁻¹.val row sourceRow * binary.val sourceColumn column
  simp only [Matrix.mul_apply, basis_matrix_entry, Prod.mk.injEq, ite_and]
  simp

theorem transformation_det (point : GeneralLinearGroup (Fin 3) ℝ) (binary : GeneralLinearGroup (Fin 2) ℝ) :
    LinearMap.det (realTransform point binary).toLinearEquiv.toLinearMap = point⁻¹.val.det ^ 2 * binary.val.det ^ 3 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun Coordinate ℝ).toBasis, transformation_matrix,
    Matrix.det_kronecker, Matrix.det_transpose]
  simp only [Fintype.card_fin]

theorem factor_eq (point : GeneralLinearGroup (Fin 3) ℝ) (binary : GeneralLinearGroup (Fin 2) ℝ) :
    RealFourierLinear.factor (realTransform point binary) = |point.val.det| ^ 2 * |binary.val.det|⁻¹ ^ 3 := by
  rw [RealFourierLinear.factor, transformation_det, mul_inv, abs_mul]
  simp only [← inv_pow, abs_pow]
  have inverseDet : point⁻¹.val.det = point.val.det⁻¹ := by
    have equality := map_inv GeneralLinearGroup.det point
    simpa only [GeneralLinearGroup.val_det_apply, Units.val_inv_eq_inv_val] using congrArg Units.val equality
  rw [inverseDet, inv_inv]
  rw [abs_inv]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFourierLinear
