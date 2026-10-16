module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Basic
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Zero
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.V2
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.X0
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.BetaClosed

@[expose] public section


/-! Clause 5 of `real_entry_tangent`. -/


namespace TernaryPeriodPolynomials.Argument

theorem real_entry_tangent_clause5 (s t : ℝ) :
    entryBeta s t (Matrix.single 0 2 1) * entryDTau s t (Matrix.single 1 2 1) -
        entryBeta s t (Matrix.single 1 2 1) * entryDTau s t (Matrix.single 0 2 1) =
      -Complex.I / (entryRadius (s, t) : ℂ) ^ 3 := by
  have hQpos : (0 : ℝ) < 1 + s ^ 2 + t ^ 2 := by positivity
  have hRne : Real.sqrt (1 + s ^ 2 + t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hQpos).ne'
  have hAne : (1 + s ^ 2 : ℝ) ≠ 0 := by positivity
  have hRHS : (-Complex.I / (entryRadius (s, t) : ℂ) ^ 3) =
      Complex.I * ((-(1 / entryRadius (s, t) ^ 3) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [entryBeta_v2_closed, entryBeta_x0_closed, entryDTau_x0, entryDTau_v2,
    hRHS, entryRadius_eq_sqrt]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring
  · simp only [Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring

end TernaryPeriodPolynomials.Argument
