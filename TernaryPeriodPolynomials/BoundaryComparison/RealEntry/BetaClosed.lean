module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Basic
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Zero
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.V2
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.X0

@[expose] public section


/-! Closed real/imaginary-part forms of `entryBeta` at `v₂` and `x₀`, in terms of `entryRadius`,
used to assemble Clause 5 of `real_entry_tangent`. -/


namespace TernaryPeriodPolynomials.Argument

theorem entryRadius_eq_sqrt (s t : ℝ) : entryRadius (s, t) = Real.sqrt (1 + s ^ 2 + t ^ 2) := rfl

theorem entryBeta_v2_closed (s t : ℝ) :
    entryBeta s t (Matrix.single 0 2 1) =
      ((-(s * t) / ((1 + s ^ 2) * entryRadius (s, t) ^ 2) : ℝ) : ℂ) +
        Complex.I * ((-(1 + s ^ 2 - t ^ 2) / ((1 + s ^ 2) * entryRadius (s, t) ^ 3) : ℝ) : ℂ) := by
  have hQpos : (0 : ℝ) < 1 + s ^ 2 + t ^ 2 := by positivity
  have hR2 : Real.sqrt (1 + s ^ 2 + t ^ 2) ^ 2 = 1 + s ^ 2 + t ^ 2 := by
    rw [← entryRadius_eq_sqrt]; exact entryRadius_sq s t
  have hRne : Real.sqrt (1 + s ^ 2 + t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hQpos).ne'
  have hAne : (1 + s ^ 2 : ℝ) ≠ 0 := by positivity
  rw [entryBeta_v2,
    gramPlaneTau_entryCurve_zero_eq' s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)),
    entryRadius_eq_sqrt]
  generalize hr_def : Real.sqrt (1 + s ^ 2 + t ^ 2) = r
  have hr2 : r ^ 2 = 1 + s ^ 2 + t ^ 2 := by rw [← hr_def]; exact hR2
  have hrne : r ≠ 0 := by rw [← hr_def]; exact hRne
  rw [← hr2]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    linear_combination (s * t) * hr2
  · simp only [Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring

theorem entryBeta_x0_closed (s t : ℝ) :
    entryBeta s t (Matrix.single 1 2 1) =
      ((t / ((1 + s ^ 2) * entryRadius (s, t) ^ 2) : ℝ) : ℂ) +
        Complex.I *
          ((-(s * (1 + s ^ 2 - t ^ 2)) / ((1 + s ^ 2) * entryRadius (s, t) ^ 3) : ℝ) : ℂ) := by
  have hQpos : (0 : ℝ) < 1 + s ^ 2 + t ^ 2 := by positivity
  have hR2 : Real.sqrt (1 + s ^ 2 + t ^ 2) ^ 2 = 1 + s ^ 2 + t ^ 2 := by
    rw [← entryRadius_eq_sqrt]; exact entryRadius_sq s t
  have hRne : Real.sqrt (1 + s ^ 2 + t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hQpos).ne'
  have hAne : (1 + s ^ 2 : ℝ) ≠ 0 := by positivity
  rw [entryBeta_x0,
    gramPlaneTau_entryCurve_zero_eq' s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)),
    entryRadius_eq_sqrt]
  generalize hr_def : Real.sqrt (1 + s ^ 2 + t ^ 2) = r
  have hr2 : r ^ 2 = 1 + s ^ 2 + t ^ 2 := by rw [← hr_def]; exact hR2
  have hrne : r ≠ 0 := by rw [← hr_def]; exact hRne
  rw [← hr2]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    linear_combination (-t) * hr2
  · simp only [Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring

end TernaryPeriodPolynomials.Argument
