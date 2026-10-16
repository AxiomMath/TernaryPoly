module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.Schwartz

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport

def matrixEquiv {ring : Type*} [CommRing ring]
    (point : GeneralLinearGroup (Fin 3) ring) (binary : GeneralLinearGroup (Fin 2) ring) :
    Rectangular ring ≃ₗ[ring] Rectangular ring where
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
  map_add' first second := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' scalar matrix := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

def matrixHomeomorph {ring : Type*} [CommRing ring] [TopologicalSpace ring] [IsTopologicalRing ring]
    (point : GeneralLinearGroup (Fin 3) ring) (binary : GeneralLinearGroup (Fin 2) ring) :
    Rectangular ring ≃ₜ Rectangular ring where
  toEquiv := (matrixEquiv point binary).toEquiv
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

noncomputable def coordinateEquiv : Rectangular ℝ ≃ₗ[ℝ] RealSpace where
  toFun matrix := WithLp.toLp 2 (fun coordinate => matrix coordinate.1 coordinate.2)
  invFun vector := fun row column => vector (row, column)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def realTransform (point : GeneralLinearGroup (Fin 3) ℝ)
    (binary : GeneralLinearGroup (Fin 2) ℝ) : RealSpace ≃L[ℝ] RealSpace :=
  ((coordinateEquiv.symm.trans (matrixEquiv point binary)).trans coordinateEquiv).toContinuousLinearEquiv

theorem realTransform_apply (point : GeneralLinearGroup (Fin 3) ℝ)
    (binary : GeneralLinearGroup (Fin 2) ℝ) (matrix : Rectangular ℝ) :
    realTransform point binary (coordinateEquiv matrix) =
      coordinateEquiv (point⁻¹.val * matrix * binary.val) := rfl

noncomputable def archimedean (matrix : Rectangular Adeles) : RealSpace :=
  coordinateEquiv (matrix.map (RingHom.fst ℝ FiniteAdeles))

noncomputable def finite (matrix : Rectangular Adeles) : Rectangular FiniteAdeles :=
  matrix.map (RingHom.snd ℝ FiniteAdeles)

theorem archimedean_rational (matrix : Rectangular ℚ) :
    archimedean (matrix.map rationalAdele) = realVector matrix := rfl

theorem finite_rational (matrix : Rectangular ℚ) :
    finite (matrix.map rationalAdele) = finiteMatrix matrix := rfl

theorem archimedean_transport (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular Adeles) :
    archimedean (point⁻¹.val * matrix * binary.val) =
      realTransform (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) point)
        (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) binary) (archimedean matrix) := by
  unfold archimedean
  rw [Matrix.map_mul, Matrix.map_mul, realTransform_apply]
  rfl

theorem finite_transport (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular Adeles) :
    finite (point⁻¹.val * matrix * binary.val) =
      matrixHomeomorph (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) point)
        (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) binary) (finite matrix) := by
  unfold finite
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
