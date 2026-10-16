module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.NilpotentInterpolation

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

theorem realNilpotentExponential_contDiff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (operator : Module.End ℂ E) (continuous : Continuous operator) (cutoff : ℕ)
    (nilpotent : operator ^ cutoff = 0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : ℝ × E => IsNilpotent.exp ((point.1 : ℂ) • operator) point.2) := by
  have powers (power : ℕ) : Continuous (operator ^ power : Module.End ℂ E) := by
    induction power with
    | zero => exact continuous_id
    | succ power hypothesis =>
      rw [pow_succ]
      exact hypothesis.comp continuous
  have term (power : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun point : ℝ × E => (point.1 ^ power / (power.factorial : ℝ)) • (operator ^ power) point.2) := by
    let linear : E →L[ℝ] E :=
      (⟨operator ^ power, powers power⟩ : E →L[ℂ] E).restrictScalars ℝ
    exact ((contDiff_fst.pow power).div_const (power.factorial : ℝ)).smul (linear.contDiff.comp contDiff_snd)
  have sum := ContDiff.sum (s := Finset.range cutoff) (fun power _ => term power)
  have equality : (fun point : ℝ × E => IsNilpotent.exp ((point.1 : ℂ) • operator) point.2) =
      (fun point => ∑ power ∈ Finset.range cutoff, (point.1 ^ power / (power.factorial : ℝ)) • (operator ^ power) point.2) := by
    funext point
    exact nilpotentExponential_real_parameter operator cutoff nilpotent point.1 point.2
  rw [equality]
  exact sum

end TernaryPeriodPolynomials.SphericalDetection.Helpers
