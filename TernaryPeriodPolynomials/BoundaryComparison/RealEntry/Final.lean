module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Basic
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Zero
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.V2
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.X0
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.BetaClosed
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Clause34
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Clause5

@[expose] public section


/-! Final assembly of `real_entry_tangent` from its five clauses. -/


namespace TernaryPeriodPolynomials.Argument

theorem real_entry_tangent_proved (s t : ℝ) :
    gramPlaneU (entryCurve s t 0 0) = (s / entryRadius (s, t) ^ 2, t / entryRadius (s, t) ^ 2) ∧
    gramPlaneTau (entryCurve s t 0 0) = entryTau (s, t) ∧
    entryDTau s t (Matrix.single 1 2 1) = s * entryDTau s t (Matrix.single 0 2 1) + 1 ∧
    entryBeta s t (Matrix.single 1 2 1) =
      s * entryBeta s t (Matrix.single 0 2 1) + ((t / entryRadius (s, t) ^ 2 : ℝ) : ℂ) ∧
    entryBeta s t (Matrix.single 0 2 1) * entryDTau s t (Matrix.single 1 2 1) -
        entryBeta s t (Matrix.single 1 2 1) * entryDTau s t (Matrix.single 0 2 1) =
      -Complex.I / (entryRadius (s, t) : ℂ) ^ 3 :=
  ⟨real_entry_tangent_clause1 s t, real_entry_tangent_clause2 s t,
    real_entry_tangent_clause3 s t, real_entry_tangent_clause4 s t,
    real_entry_tangent_clause5 s t⟩

end TernaryPeriodPolynomials.Argument
