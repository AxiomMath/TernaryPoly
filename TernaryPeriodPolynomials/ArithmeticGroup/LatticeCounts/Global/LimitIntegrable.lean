module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitBound
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitEuler
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitExhaust
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitMeas
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBound

@[expose] public section


/-!
# Global limit: integrability of the global integrand and convergence of the finite integrals

For `k = -2 · halfWeight > 6` and `det g∞ > 0`: the global integrand is integrable on `FiniteAwayThree²` for the product Haar measure, and
`∫_{U_S} F → ∫ F` along finite sets `S` of primes `≠ 3`.  The proof is `GlobalLimitAbstract.exhaust_integrable_tendsto` with the uniform bound
`∫_{U_S} ‖F‖ ≤ Cc · M` (`GlobalLimitBound.lintegral_UregionS_le`, `GlobalLimitEuler.euler_bound`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Filter Topology Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped ENNReal
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitPointwise
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitBound
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitEuler
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitExhaust
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitMeas
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitAbstract

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitIntegrable

variable {σ : CuspidalRepresentation} {n : ℕ}

theorem bexp_gt (I : EichlerInput σ n) (hk : 6 < -2 * I.halfWeight) : 3 < bexp I := by
  unfold bexp
  have : (6 : ℝ) < ((-2 * I.halfWeight : ℤ) : ℝ) := by exact_mod_cast hk
  linarith

/-- **Integrability and convergence of the finite integrals.** -/
theorem globalIntegrand_integrable_tendsto (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (hk : 6 < -2 * I.halfWeight) (gInf : BinaryRealGL) (hg : (Matrix.GeneralLinearGroup.det gInf).val ≠ 0)
    (Z : BinaryFiniteGL) (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val) :
    Integrable (globalIntegrand I Z gInf) (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      Tendsto (fun T : Finset PIdx => ∫ z in Uex T, globalIntegrand I Z gInf z
          ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) atTop
        (𝓝 (∫ z, globalIntegrand I Z gInf z ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))) := by
  have hb := bexp_gt I hk
  obtain ⟨C, hC0, hC⟩ := TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBound.norm_Fh_le
    (-2 * I.halfWeight) h
  obtain ⟨M, hM⟩ := euler_bound (bexp I) hb
  set Cc : ℝ := ‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det Z)) (expo I)‖ * C with hCc
  have hCc0 : 0 ≤ Cc := mul_nonneg (norm_nonneg _) hC0
  refine exhaust_integrable_tendsto (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) Uex Uex_measurable
    Uex_mono (fun z => Uex_cover z) (globalIntegrand I Z gInf)
    (globalIntegrand_measurable I Z hZ gInf).aestronglyMeasurable (Real.toNNReal (Cc * M)) fun T => ?_
  refine (lintegral_UregionS_le I h hform gInf hg hC0 hC Z hZ hb (SEP T) (SEP_ne T)).trans ?_
  have := hM (SEP T)
  calc ENNReal.ofReal Cc * ∏ w ∈ SEP T, _ ≤ ENNReal.ofReal Cc * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (Cc * M) := (ENNReal.ofReal_mul hCc0).symm
    _ = _ := rfl

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitIntegrable
