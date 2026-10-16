module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Haar
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.FibreMeasure
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LtBij

@[expose] public section


/-!
# Fibre measure of `L_t` for cyclic Hermite triples

Formalized by Claude Haiku 5.5.

For `t ∈ cyclicHNF q r` (`r ≥ 1`), the shell points `z` whose lattice `pairLat q z` equals
`L_t = hermLat q t` have measure `q^r - q^(r-1)` under the product of a normalized additive Haar
measure on `ℚ_q`. This is `shell_fibre_measure` applied to `L_t`, which is cyclic of index `q^r`
by `hermLat_index_cyclic`. The finite-place version mirrors `shell_measure_finitePlace`.
-/

open MeasureTheory GeneralEisenstein.Adelic TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts (cyclicHNF)

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

/-- **Fibre measure of `L_t`.** For `t ∈ cyclicHNF q r` with `r ≥ 1`, the shell points with lattice
`L_t` have product measure `q^r - q^(r-1)`, for a normalized additive Haar measure `μ₁`. -/
theorem hermLat_fibre_measure (q : ℕ) [Fact q.Prime] [MeasurableSpace ℚ_[q]] [BorelSpace ℚ_[q]]
    [MeasurableAdd ℚ_[q]] {μ₁ : Measure ℚ_[q]} [SigmaFinite μ₁] [μ₁.IsAddLeftInvariant]
    (h1 : μ₁ {x | ‖x‖ ≤ 1} = 1) {r : ℕ} (hr : 1 ≤ r) {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF q r) :
    (μ₁.prod μ₁)
        {z | z ∈ pairShell q r ∧ (pairLat q z).toAddSubgroup = (hermLat q t).toAddSubgroup} =
      ((q ^ r - q ^ (r - 1) : ℕ) : ENNReal) := by
  obtain ⟨hi, hc⟩ := hermLat_index_cyclic ht
  exact shell_fibre_measure (prod_measure_Zp2 q h1) hr hi hc

/-- **Fibre measure of `L_t` at a finite place.** The measure is `finitePadicMeasure place`
squared, with `vol(ℤ_q) = 1` supplied by the library, so no normalization hypothesis is needed. -/
theorem hermLat_fibre_measure_finitePlace (place : FinitePlace) {r : ℕ} (hr : 1 ≤ r)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF (Rat.HeightOneSpectrum.primesEquiv place).val r) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (finitePadicMeasure place).prod (finitePadicMeasure place)
        {z | z ∈ pairShell (Rat.HeightOneSpectrum.primesEquiv place).val r ∧
          (pairLat (Rat.HeightOneSpectrum.primesEquiv place).val z).toAddSubgroup =
            (hermLat (Rat.HeightOneSpectrum.primesEquiv place).val t).toAddSubgroup} =
      ((((Rat.HeightOneSpectrum.primesEquiv place).val ^ r -
        (Rat.HeightOneSpectrum.primesEquiv place).val ^ (r - 1) : ℕ)) : ENNReal) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  exact hermLat_fibre_measure (Rat.HeightOneSpectrum.primesEquiv place).val
    (finitePadicMeasure_normalized place) hr ht

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
