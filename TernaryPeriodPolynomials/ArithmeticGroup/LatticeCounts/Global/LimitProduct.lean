module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitPointwise
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitShape
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitAbstract
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PadicMeasures

@[expose] public section


/-!
# Global limit: the integral of the product weight

`lintegral_pi_pair`: for a finite family of measurable `g_i` on `E_i × E_i`, the integral of `∏ g_i (x_i, y_i)` over
`(Measure.pi μ) ⊗ (Measure.pi μ)` is `∏ ∫ g_i d(μ_i ⊗ μ_i)`.  `lintegral_phiW_le`: the local factor
`∫ phiW d(μ_w ⊗ μ_w) ≤ (1 - p^(2-b))⁻¹` for `b = k/2 > 3`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open scoped ENNReal
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitLocal
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitPointwise
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitAbstract

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitProduct

variable {σ : CuspidalRepresentation} {n : ℕ}

theorem lintegral_pi_pair {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] (g : ∀ i, E i × E i → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : (∀ i, E i) × (∀ i, E i), ∏ i, g i (x.1 i, x.2 i) ∂((Measure.pi μ).prod (Measure.pi μ)) =
      ∏ i, ∫⁻ y, g i y ∂((μ i).prod (μ i)) := by
  have hmeas : Measurable (fun x : (∀ i, E i) × (∀ i, E i) => ∏ i, g i (x.1 i, x.2 i)) :=
    Finset.measurable_prod _ fun i _ => (hg i).comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))
  rw [lintegral_prod _ hmeas.aemeasurable]
  have h1 : ∀ x : ∀ i, E i, ∫⁻ y, ∏ i, g i (x i, y i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, g i (x i, y) ∂(μ i) :=
    fun x => lintegral_fintype_prod_eq_prod (fun i y => g i (x i, y)) fun i => (hg i).comp measurable_prodMk_left
  simp_rw [h1]
  have h2 := lintegral_fintype_prod_eq_prod (μ := μ) (fun i a => ∫⁻ y, g i (a, y) ∂(μ i))
    fun i => (hg i).lintegral_prod_right'
  rw [h2]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_prod _ (hg i).aemeasurable]

/-- **The local factor.** -/
theorem lintegral_phiW_le (I : EichlerInput σ n) (hb : 3 < bexp I) (w : FinitePlace) :
    ∫⁻ x : w.adicCompletion ℚ × w.adicCompletion ℚ, ENNReal.ofReal (phiW I w x.1 x.2)
        ∂((finiteCompletionMeasure w).prod (finiteCompletionMeasure w)) ≤
      ENNReal.ofReal ((1 - (((Rat.HeightOneSpectrum.primesEquiv w).val : ℕ) : ℝ) ^ (2 - bexp I))⁻¹) := by
  have hmp := (finiteCompletionPadic_measurePreserving w).prod (finiteCompletionPadic_measurePreserving w)
  have hmeas : Measurable (fun z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv w).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv w).val] => ENNReal.ofReal (phiR _ (bexp I) z)) :=
    ENNReal.measurable_ofReal.comp (phiR_measurable _ _)
  have := hmp.lintegral_comp hmeas
  exact this.le.trans (lintegral_phiR_le _ (bexp I) hb (finitePadicMeasure_normalized w))

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitProduct
