module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.Lattice

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularLattice

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactTheta

noncomputable def transform (point : AdelicGL) (binary : BinaryAdelicGL) :
    Rectangular Adeles ≃ₜ Rectangular Adeles where
  toFun matrix := point⁻¹.val * matrix * binary.val
  invFun matrix := point.val * matrix * binary⁻¹.val
  left_inv matrix := by
    change point.val * (point⁻¹.val * matrix * binary.val) * binary⁻¹.val = matrix
    have pointInverse : point.val * point⁻¹.val = 1 := point.val_inv
    have binaryInverse : binary.val * binary⁻¹.val = 1 := binary.val_inv
    rw [← Matrix.mul_assoc point.val, ← Matrix.mul_assoc point.val, pointInverse,
      Matrix.one_mul, Matrix.mul_assoc, binaryInverse, Matrix.mul_one]
  right_inv matrix := by
    change point⁻¹.val * (point.val * matrix * binary⁻¹.val) * binary.val = matrix
    have pointInverse : point⁻¹.val * point.val = 1 := point.inv_val
    have binaryInverse : binary⁻¹.val * binary.val = 1 := binary.inv_val
    rw [← Matrix.mul_assoc point⁻¹.val, ← Matrix.mul_assoc point⁻¹.val, pointInverse,
      Matrix.one_mul, Matrix.mul_assoc, binaryInverse, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem finite_support (test : Rectangular Adeles → ℂ) (compactSupport : HasCompactSupport test)
    (point : AdelicGL) (binary : BinaryAdelicGL) :
    (Function.support (matrixTerm test point binary)).Finite := by
  have compactPullback := compactSupport.comp_homeomorph (transform point binary)
  apply (finite_in_compact (tsupport (test ∘ transform point binary)) compactPullback).subset
  intro matrix membership
  exact subset_closure membership

theorem summable (test : Rectangular Adeles → ℂ) (compactSupport : HasCompactSupport test)
    (point : AdelicGL) (binary : BinaryAdelicGL) : Summable (matrixTerm test point binary) :=
  summable_of_hasFiniteSupport (finite_support test compactSupport point binary)

theorem summable_norm (test : Rectangular Adeles → ℂ) (compactSupport : HasCompactSupport test)
    (point : AdelicGL) (binary : BinaryAdelicGL) : Summable (fun matrix => ‖matrixTerm test point binary matrix‖) := by
  apply summable_of_hasFiniteSupport
  apply (finite_support test compactSupport point binary).subset
  intro matrix membership
  simpa only [Function.mem_support, norm_ne_zero_iff] using membership

theorem fullTheta_decomposition (test : Rectangular Adeles → ℂ) (compactSupport : HasCompactSupport test)
    (point : AdelicGL) (binary : BinaryAdelicGL) :
    fullTheta test point binary = RectangularKernel.theta test point binary + singularTheta test point binary :=
  decomposition test point binary (summable test compactSupport point binary)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactTheta
