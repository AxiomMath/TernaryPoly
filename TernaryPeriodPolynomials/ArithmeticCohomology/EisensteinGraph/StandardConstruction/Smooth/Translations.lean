module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Continuity
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmoothTranslations

def tupleRightMul {size arity : ℕ}
    (right : Fin arity → Matrix (Fin size) (Fin size) ℝ) :
    (Fin arity → Matrix (Fin size) (Fin size) ℝ) →ₗ[ℝ]
      (Fin arity → Matrix (Fin size) (Fin size) ℝ) where
  toFun matrices index := matrices index * right index
  map_add' first second := by
    funext index
    exact Matrix.add_mul _ _ _
  map_smul' scalar matrices := by
    funext index
    exact Matrix.smul_mul scalar (matrices index) (right index)

theorem invertibleMatrix_mul_right {size : ℕ}
    (matrix : Matrix (Fin size) (Fin size) ℝ) (invertible : matrix.det ≠ 0)
    (right : GeneralLinearGroup (Fin size) ℝ) :
    invertibleMatrix (matrix * right.val) = invertibleMatrix matrix * right := by
  have productInvertible : (matrix * right.val).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero invertible (GeneralLinearGroup.det_ne_zero right)
  unfold invertibleMatrix
  rw [dite_eq_left productInvertible, dite_eq_left invertible]
  apply Units.ext
  rfl

theorem smooth_mul_right {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E)
    (smooth : Smooth function) (right : Fin arity → GeneralLinearGroup (Fin size) ℝ) :
    Smooth (fun elements => function (fun index => elements index * right index)) := by
  have matrixSmooth : ContDiff ℝ ⊤ (fun matrices : Fin arity → Matrix (Fin size) (Fin size) ℝ =>
      fun index => matrices index * (right index).val) :=
    (tupleRightMul (fun index => (right index).val)).toContinuousLinearMap.contDiff
  have maps : Set.MapsTo (fun matrices : Fin arity → Matrix (Fin size) (Fin size) ℝ =>
      fun index => matrices index * (right index).val)
      {matrices | ∀ index, (matrices index).det ≠ 0}
      {matrices | ∀ index, (matrices index).det ≠ 0} := by
    intro matrices membership index
    rw [Matrix.det_mul]
    exact mul_ne_zero (membership index) (GeneralLinearGroup.det_ne_zero (right index))
  apply (smooth.comp matrixSmooth.contDiffOn maps).congr
  intro matrices membership
  dsimp only [Function.comp_def]
  congr 1
  funext index
  exact (invertibleMatrix_mul_right (matrices index) (membership index) (right index)).symm

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmoothTranslations
