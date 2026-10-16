module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.FourierLinear

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularOperatorBounds

instance binaryOperatorNorm : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] RealSpace →L[ℝ] RealSpace) :=
  ContinuousLinearMap.toNormedAddCommGroup

instance binaryOperatorSpace : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] RealSpace →L[ℝ] RealSpace) :=
  ContinuousLinearMap.toNormedSpace

instance bilinearOperatorNorm :
    NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] RealSpace →L[ℝ] RealSpace) :=
  ContinuousLinearMap.toNormedAddCommGroup

def action (left : Matrix (Fin 3) (Fin 3) ℝ) (right : Matrix (Fin 2) (Fin 2) ℝ) : RealSpace →L[ℝ] RealSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun vector => coordinateEquiv (left * coordinateEquiv.symm vector * right)
      map_add' := by intros; simp only [map_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intros; simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }

theorem action_apply (left : Matrix (Fin 3) (Fin 3) ℝ) (right : Matrix (Fin 2) (Fin 2) ℝ) (vector : RealSpace) :
    action left right vector = coordinateEquiv (left * coordinateEquiv.symm vector * right) := rfl

def bilinearMap : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] RealSpace →L[ℝ] RealSpace :=
  LinearMap.mk₂ ℝ action
    (by intros; apply ContinuousLinearMap.ext; intro vector; simp only [action_apply, Matrix.add_mul, map_add, _root_.add_apply])
    (by intros; apply ContinuousLinearMap.ext; intro vector; simp only [action_apply, Matrix.smul_mul, map_smul, _root_.smul_apply])
    (by intros; apply ContinuousLinearMap.ext; intro vector; simp only [action_apply, Matrix.mul_add, map_add, _root_.add_apply])
    (by intros; apply ContinuousLinearMap.ext; intro vector; simp only [action_apply, Matrix.mul_smul, map_smul, _root_.smul_apply])

def bilinear : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] RealSpace →L[ℝ] RealSpace :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Matrix (Fin 3) (Fin 3) ℝ)
    (F' := Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] RealSpace →L[ℝ] RealSpace)
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Matrix (Fin 2) (Fin 2) ℝ)
      (F' := RealSpace →L[ℝ] RealSpace)).toLinearMap.comp bilinearMap)

theorem bilinear_apply (left : Matrix (Fin 3) (Fin 3) ℝ) (right : Matrix (Fin 2) (Fin 2) ℝ) :
    bilinear left right = action left right := rfl

theorem norm_action (left : Matrix (Fin 3) (Fin 3) ℝ) (right : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖action left right‖ ≤ ‖bilinear‖ * ‖left‖ * ‖right‖ := by
  rw [← bilinear_apply]
  exact ((bilinear left).le_opNorm right).trans
    (mul_le_mul_of_nonneg_right (bilinear.le_opNorm left) (norm_nonneg _))

theorem norm_transform (point : GeneralLinearGroup (Fin 3) ℝ) (binary : GeneralLinearGroup (Fin 2) ℝ) :
    ‖(realTransform point binary).toContinuousLinearMap‖ ≤ ‖bilinear‖ * ‖point⁻¹.val‖ * ‖binary.val‖ :=
  norm_action point⁻¹.val binary.val

theorem norm_inverse (point : GeneralLinearGroup (Fin 3) ℝ) (binary : GeneralLinearGroup (Fin 2) ℝ) :
    ‖(realTransform point binary).symm.toContinuousLinearMap‖ ≤ ‖bilinear‖ * ‖point.val‖ * ‖binary⁻¹.val‖ :=
  norm_action point.val binary⁻¹.val

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularOperatorBounds
