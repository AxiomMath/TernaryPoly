module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Count
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PadicMeasures

@[expose] public section


/-!
# The shell measure for the paper's local Haar measure, with no normalization hypothesis

Formalized by Claude Haiku 5.5. Follow-up to
`Padic.shell_measure` (`LatticeCounts/ShellCount.lean`), which takes `μ(ℤ_p²) = 1` as a hypothesis.

The library's finite-place measure `finitePadicMeasure place` on `ℚ_[(primesEquiv place).val]`
is additive Haar and gives the closed unit ball measure one (`finitePadicMeasure_normalized`).
Its square is the product measure on `ℚ_p²`, and `ℤ_p² = (ball) ×ˢ (ball)` has measure one for it.
So the hypothesis `hn` of `Padic.shell_measure` is discharged here by the library's own measure.
-/

open MeasureTheory GeneralEisenstein.Adelic TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

/-- For a normalized additive Haar measure `μ₁` on `ℚ_p` (the unit ball has measure one), the
product measure gives `ℤ_p² = Zp2 p` measure one. -/
theorem prod_measure_Zp2 (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    {μ₁ : Measure ℚ_[p]} [SigmaFinite μ₁] (h1 : μ₁ {x | ‖x‖ ≤ 1} = 1) :
    (μ₁.prod μ₁) (Zp2 p) = 1 := by
  have e : Zp2 p = {x : ℚ_[p] | ‖x‖ ≤ 1} ×ˢ {x : ℚ_[p] | ‖x‖ ≤ 1} := by
    ext z
    simp [Zp2]
  rw [e, Measure.prod_prod, h1, mul_one]

/-- The shell measure for a normalized additive Haar measure `μ₁` on `ℚ_p`, with the product
measure on `ℚ_p²`. No hypothesis beyond normalization of `μ₁`. -/
theorem shell_measure_prod (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    [MeasurableAdd ℚ_[p]] {μ₁ : Measure ℚ_[p]} [SigmaFinite μ₁] [μ₁.IsAddLeftInvariant]
    (h1 : μ₁ {x | ‖x‖ ≤ 1} = 1) {r : ℕ} (hr : 1 ≤ r) :
    (μ₁.prod μ₁) (pairShell p r) = ((p ^ (2 * r) - p ^ (2 * r - 2) : ℕ) : ENNReal) :=
  shell_measure (prod_measure_Zp2 p h1) hr

/-- The shell measure for a normalized Haar measure, in the rational form `(1 - p⁻²) p^(2r)`. -/
theorem shell_measure_prod_rat (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    [MeasurableAdd ℚ_[p]] {μ₁ : Measure ℚ_[p]} [SigmaFinite μ₁] [μ₁.IsAddLeftInvariant]
    (h1 : μ₁ {x | ‖x‖ ≤ 1} = 1) {r : ℕ} (hr : 1 ≤ r) :
    (μ₁.prod μ₁) (pairShell p r) =
      ENNReal.ofReal ((1 - ((p : ℝ) ^ 2)⁻¹) * (p : ℝ) ^ (2 * r)) :=
  shell_measure_rat (prod_measure_Zp2 p h1) hr

/-- **The shell measure for the paper's local Haar measure at a finite place.** The measure is
`finitePadicMeasure place` squared, with `vol(ℤ_p) = 1` supplied by the library
(`finitePadicMeasure_normalized`), so the statement carries no normalization hypothesis. -/
theorem shell_measure_finitePlace (place : FinitePlace) {r : ℕ} (hr : 1 ≤ r) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (finitePadicMeasure place).prod (finitePadicMeasure place)
        (pairShell (Rat.HeightOneSpectrum.primesEquiv place).val r) =
      ((((Rat.HeightOneSpectrum.primesEquiv place).val ^ (2 * r) -
        (Rat.HeightOneSpectrum.primesEquiv place).val ^ (2 * r - 2) : ℕ)) : ENNReal) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  exact shell_measure_prod (Rat.HeightOneSpectrum.primesEquiv place).val
    (μ₁ := finitePadicMeasure place) (finitePadicMeasure_normalized place) hr

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
