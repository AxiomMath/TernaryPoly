module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Basic
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Zero
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.V2
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.X0

@[expose] public section


/-! Clauses 3 and 4 of `real_entry_tangent`. -/


namespace TernaryPeriodPolynomials.Argument

theorem real_entry_tangent_clause3 (s t : ℝ) :
    entryDTau s t (Matrix.single 1 2 1) = s * entryDTau s t (Matrix.single 0 2 1) + 1 := by
  rw [entryDTau_x0, entryDTau_v2]
  have hne : (1 + s ^ 2 : ℝ) ≠ 0 := by positivity
  have hA : (1 / (1 + s ^ 2) : ℝ) = s * (-s / (1 + s ^ 2)) + 1 := by
    field_simp
    ring
  have hB : (s * t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) =
      s * (t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2)) := by
    ring
  rw [hA, hB]
  push_cast
  ring

theorem real_entry_tangent_clause4 (s t : ℝ) :
    entryBeta s t (Matrix.single 1 2 1) =
      s * entryBeta s t (Matrix.single 0 2 1) +
        ((t / entryRadius (s, t) ^ 2 : ℝ) : ℂ) := by
  rw [entryBeta_x0, entryBeta_v2, entryRadius_sq,
    gramPlaneTau_entryCurve_zero_eq s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)),
    gramPlaneTau_entryCurve_zero_eq s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ))]
  have hQne : (1 + s ^ 2 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have hT1 : (t * (1 - s ^ 2 + t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2 : ℝ) =
      s * (-(2 * s * t) / (1 + s ^ 2 + t ^ 2) ^ 2) + t / (1 + s ^ 2 + t ^ 2) := by
    field_simp
    ring
  have hT2 : (s * (1 + s ^ 2 - t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2 : ℝ) =
      s * ((1 + s ^ 2 - t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2) := by
    ring
  rw [hT1, hT2]
  push_cast
  ring

end TernaryPeriodPolynomials.Argument
