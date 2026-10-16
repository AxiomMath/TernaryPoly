module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionContinuity
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem invertibleMatrixTuples_isOpen (size arity : ℕ) :
    IsOpen {matrices : Fin arity → Matrix (Fin size) (Fin size) ℝ |
      ∀ index, (matrices index).det ≠ 0} := by
  have equality : {matrices : Fin arity → Matrix (Fin size) (Fin size) ℝ |
      ∀ index, (matrices index).det ≠ 0} =
      ⋂ index, {matrices | (matrices index).det ≠ 0} := by ext; simp
  rw [equality]
  exact isOpen_iInter_of_finite fun index =>
    isOpen_ne.preimage (continuous_apply index).matrix_det

theorem smooth_contDiffAt_matrix {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E}
    (smooth : Smooth function) (matrices : Fin arity → GeneralLinearGroup (Fin size) ℝ) :
    ContDiffAt ℝ ⊤
      (fun entries : Fin arity → Matrix (Fin size) (Fin size) ℝ =>
        function (fun index => invertibleMatrix (entries index)))
      (fun index => (matrices index).val) :=
  smooth.contDiffAt ((invertibleMatrixTuples_isOpen size arity).mem_nhds
    (fun index => (matrices index).det_ne_zero))

theorem smooth_iteratedFDeriv_continuous {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E}
    (smooth : Smooth function) (order : ℕ) :
    Continuous (fun matrices : Fin arity → GeneralLinearGroup (Fin size) ℝ =>
      iteratedFDeriv ℝ order
        (fun entries : Fin arity → Matrix (Fin size) (Fin size) ℝ =>
          function (fun index => invertibleMatrix (entries index)))
        (fun index => (matrices index).val)) := by
  exact (ContinuousOn.continuousOn_iteratedFDeriv smooth
      (invertibleMatrixTuples_isOpen size arity) le_top).comp_continuous
    (continuous_pi (fun index => Units.continuous_val.comp (continuous_apply index)))
    (fun matrices index => (matrices index).det_ne_zero)

theorem smooth_iteratedFDeriv_compact_bound {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E}
    (smooth : Smooth function) (order : ℕ)
    {domain : Set (Fin arity → GeneralLinearGroup (Fin size) ℝ)}
    (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ matrices ∈ domain,
      ‖iteratedFDeriv ℝ order
        (fun entries : Fin arity → Matrix (Fin size) (Fin size) ℝ =>
          function (fun index => invertibleMatrix (entries index)))
        (fun index => (matrices index).val)‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn
    (smooth_iteratedFDeriv_continuous smooth order).continuousOn
  exact ⟨max 0 bound, le_max_left _ _, fun matrices member =>
    (bounded matrices member).trans (le_max_right _ _)⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
