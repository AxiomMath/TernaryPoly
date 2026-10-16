module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Cholesky
public import Mathlib.Topology.Instances.Matrix

@[expose] public section


/-!
# Continuity of the Cholesky factor

`cholDomain` (positive trailing principal minors) is the domain of `cholLine`; its entries and hence `cholLine`
are continuous on it.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The open set of matrices with positive trailing principal minors. -/
def cholDomain : Set Mat3 := {P | 0 < P 2 2 ∧ 0 < P 1 1 * P 2 2 - P 1 2 ^ 2 ∧ 0 < P.det}

theorem entry_continuous' (i j : Fin 3) : Continuous (fun P : Mat3 => P i j) :=
  (continuous_apply j).comp (continuous_apply i)

theorem continuousOn_cholC11 : ContinuousOn cholC11 cholDomain :=
  Real.continuous_sqrt.comp_continuousOn (entry_continuous' 2 2).continuousOn

theorem continuousOn_cholC00 : ContinuousOn cholC00 cholDomain := by
  refine Real.continuous_sqrt.comp_continuousOn ?_
  refine ContinuousOn.div ?_ (entry_continuous' 2 2).continuousOn (fun P hP => hP.1.ne')
  exact (((entry_continuous' 1 1).mul (entry_continuous' 2 2)).sub ((entry_continuous' 1 2).pow 2)).continuousOn

theorem continuousOn_cholA : ContinuousOn cholA cholDomain := by
  refine Real.continuous_sqrt.comp_continuousOn ?_
  refine ContinuousOn.div (Continuous.matrix_det continuous_id).continuousOn ?_ (fun P hP => hP.2.1.ne')
  exact (((entry_continuous' 1 1).mul (entry_continuous' 2 2)).sub ((entry_continuous' 1 2).pow 2)).continuousOn

theorem continuousOn_cholB1 : ContinuousOn cholB1 cholDomain := by
  unfold cholB1
  exact (entry_continuous' 0 2).continuousOn.div continuousOn_cholC11
    (fun P hP => (Real.sqrt_pos.mpr hP.1).ne')

theorem continuousOn_cholC01 : ContinuousOn cholC01 cholDomain := by
  unfold cholC01
  exact (entry_continuous' 1 2).continuousOn.div continuousOn_cholC11
    (fun P hP => (Real.sqrt_pos.mpr hP.1).ne')

theorem continuousOn_cholB0 : ContinuousOn cholB0 cholDomain := by
  unfold cholB0
  refine ContinuousOn.div ?_ continuousOn_cholC00 (fun P hP => (cholC00_pos P hP.1 hP.2.1).ne')
  exact (entry_continuous' 0 1).continuousOn.sub
    (((entry_continuous' 0 2).continuousOn.div continuousOn_cholC11
      (fun P hP => (Real.sqrt_pos.mpr hP.1).ne')).mul
    ((entry_continuous' 1 2).continuousOn.div continuousOn_cholC11
      (fun P hP => (Real.sqrt_pos.mpr hP.1).ne')))

theorem continuousOn_cholLine : ContinuousOn cholLine cholDomain := by
  refine continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;> simp only [cholLine, Fin.zero_eta, Fin.mk_one, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
    first
      | exact continuousOn_cholA | exact continuousOn_cholB0 | exact continuousOn_cholB1
      | exact continuousOn_cholC00 | exact continuousOn_cholC01 | exact continuousOn_cholC11
      | exact continuousOn_const

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
