module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitProduct

@[expose] public section


/-!
# Global limit: the bound on `∫_{U_S} ‖F‖` by a product of local factors

For a finite set `S` of places `≠ 3`:
`∫_{U_S} ‖F‖ ≤ Cc · ∏_{w∈S} (1 - p_w^(2-k/2))⁻¹`, `Cc = ‖normPower(det Z) b‖ · C`.  The pointwise bound is
`GlobalLimitPointwise.norm_globalIntegrand_le`, the shape lemma `setLIntegral_UregionS` turns the integral over `U_S` into one over the `S`-local coordinates,
and `lintegral_pi_pair` with `lintegral_phiW_le` evaluates it.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped ENNReal
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwaySplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitLocal
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitPointwise
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitProduct
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary (Fh)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitBound

variable {σ : CuspidalRepresentation} {n : ℕ}

theorem phiW_measurable (I : EichlerInput σ n) (w : FinitePlace) :
    Measurable (fun x : w.adicCompletion ℚ × w.adicCompletion ℚ => phiW I w x.1 x.2) := by
  have h1 : Measurable (pe w) := (finiteCompletionPadicAddEquiv w).continuous.measurable
  exact (phiR_measurable _ _).comp ((h1.comp measurable_fst).prodMk (h1.comp measurable_snd))

theorem phiW_nonneg (I : EichlerInput σ n) (w : FinitePlace) (a b : w.adicCompletion ℚ) : 0 ≤ phiW I w a b :=
  phiR_nonneg _ _ _

theorem coord_measurable (I : EichlerInput σ n) (S : Finset FinitePlace) (p : S) :
    Measurable (fun a : WS S × WS S => ENNReal.ofReal (phiW I p.1 (a.1 p) (a.2 p))) := by
  have h2 : Measurable (fun a : WS S × WS S => (a.1 p, a.2 p)) :=
    ((measurable_pi_apply p).comp measurable_fst).prodMk ((measurable_pi_apply p).comp measurable_snd)
  have h3 := (phiW_measurable I p.1).comp h2
  exact ENNReal.measurable_ofReal.comp h3

theorem lintegral_UregionS_le (I : EichlerInput σ n) (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : (Matrix.GeneralLinearGroup.det gInf).val ≠ 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ g : GL (Fin 2) ℝ, 0 < (Matrix.GeneralLinearGroup.det g).val → ‖Fh (-2 * I.halfWeight) ⇑h g‖ ≤ C)
    (Z : BinaryFiniteGL) (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (hb : 3 < bexp I) (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) :
    ∫⁻ z in UregionS S, ‖globalIntegrand I Z gInf z‖ₑ ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ≤
      ENNReal.ofReal (‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det Z)) (expo I)‖ * C) *
        ∏ w ∈ S, ENNReal.ofReal
          ((1 - (((Rat.HeightOneSpectrum.primesEquiv w).val : ℕ) : ℝ) ^ (2 - bexp I))⁻¹) := by
  set Cc : ℝ := ‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det Z)) (expo I)‖ * C with hCc
  have hCc0 : 0 ≤ Cc := mul_nonneg (norm_nonneg _) hC0
  let G : WS S × WS S → ℝ≥0∞ := fun a =>
    ENNReal.ofReal Cc * ∏ p : S, ENNReal.ofReal (phiW I p.1 (a.1 p) (a.2 p))
  have hGm : Measurable G := by
    exact measurable_const.mul (Finset.measurable_prod _ fun p _ => coord_measurable I S p)
  calc ∫⁻ z in UregionS S, ‖globalIntegrand I Z gInf z‖ₑ ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)
      ≤ ∫⁻ z in UregionS S, G (piS S z.1, piS S z.2) ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
        refine setLIntegral_mono' (UregionS_measurable S hS) fun z hz => ?_
        have hp := norm_globalIntegrand_le I h hform gInf hg hC Z hZ S hz
        rw [← ofReal_norm]
        refine (ENNReal.ofReal_le_ofReal hp).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul hCc0, ENNReal.ofReal_prod_of_nonneg
          (fun w _ => phiW_nonneg I w _ _)]
        simp only [G]
        congr 1
        exact (Finset.prod_coe_sort S (fun w => ENNReal.ofReal (phiW I w (finiteEvaluation w (awayVal z.1))
          (finiteEvaluation w (awayVal z.2))))).symm
    _ = ∫⁻ a, G a ∂((localPi S).prod (localPi S)) := setLIntegral_UregionS S hS G hGm
    _ = ENNReal.ofReal Cc * ∏ p : S, ∫⁻ y, ENNReal.ofReal (phiW I p.1 y.1 y.2)
          ∂((finiteCompletionMeasure p.1).prod (finiteCompletionMeasure p.1)) := by
        simp only [G]
        rw [lintegral_const_mul _ (Finset.measurable_prod _ fun p _ => coord_measurable I S p)]
        congr 1
        exact lintegral_pi_pair (μ := fun p : S => finiteCompletionMeasure p.1)
          (fun p y => ENNReal.ofReal (phiW I p.1 y.1 y.2))
          fun p => ENNReal.measurable_ofReal.comp (phiW_measurable I p.1)
    _ ≤ ENNReal.ofReal Cc * ∏ p : S, ENNReal.ofReal
          ((1 - (((Rat.HeightOneSpectrum.primesEquiv p.1).val : ℕ) : ℝ) ^ (2 - bexp I))⁻¹) := by
        gcongr with p _
        exact lintegral_phiW_le I hb p.1
    _ = _ := by rw [Finset.prod_coe_sort S (fun w => ENNReal.ofReal
          ((1 - (((Rat.HeightOneSpectrum.primesEquiv w).val : ℕ) : ℝ) ^ (2 - bexp I))⁻¹))]

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitBound
