module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TopologicalMatrices
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmoothContinuity

theorem invertibleMatrix_coe {size : ℕ} (element : GeneralLinearGroup (Fin size) ℝ) :
    invertibleMatrix element.val = element := by
  have nonzero : element.val.det ≠ 0 := (GeneralLinearGroup.det element).ne_zero
  unfold invertibleMatrix
  rw [dite_eq_left nonzero]
  apply Units.ext
  rfl

theorem smooth_continuous {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E)
    (smooth : Smooth function) : Continuous function := by
  have coeContinuous : Continuous (fun elements : Fin arity → GeneralLinearGroup (Fin size) ℝ =>
      fun index => (elements index).val) := by
    apply continuous_pi
    intro index
    exact Units.continuous_val.comp (continuous_apply index)
  have composed := smooth.continuousOn.comp_continuous coeContinuous (fun elements index =>
    (GeneralLinearGroup.det (elements index)).ne_zero)
  simpa only [Function.comp_def, invertibleMatrix_coe] using composed

theorem induced_real_continuous {degree : ℕ} (data : InducingData degree)
    (side : Side) (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (argument : AdelicGL) :
    Continuous (fun real : RealGL3 => function (argument * atInfinity real)) := by
  have continuous := smooth_continuous _ (induced.1 argument)
  have constantTuple : Continuous (fun real : RealGL3 => fun _ : Fin 1 => real) :=
    continuous_pi (fun _ => continuous_id)
  exact continuous.comp constantTuple

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmoothContinuity
