module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LineStepNeg
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LineStepCq
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitMain

@[expose] public section


/-!
# The global integral as the Euler product, unconditionally

`lineStep_cq` (any `det g∞ ≠ 0`): H4's `LineStepCq.lineStep_cq_pos` for `0 < det g∞`; for `det g∞ < 0`, `LineStepNeg.lineStep_neg_of_pos` applied to the reflected data `(RZR, Rg∞)`.
`global_integral_euler`: for `k = -2 · halfWeight > 6`, `det g∞ ≠ 0`, `Z` integral at every place and `h` a normalized eigenform realized by the input, `F` is integrable on `FiniteAwayThree²` and
`∫ F = normPower(det Z)(k/2) · vhValueFull k h g∞ Z · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)`.  No hypothesis other than the paper's.

Formalized by Claude Sonnet 5.5, with Claude Haiku 5.5.
-/

open MeasureTheory Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitExhaust
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitInduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitMain
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg (vhValueFull reflectionQ det_reflectionQ_real)
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction (binaryRationalReal binaryRationalFinite)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LineStepNeg
open TernaryPeriodPolynomials.Argument.LatticeCounts.LineStepCq

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitUncond

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- **The line step for every `det g∞ ≠ 0`.** -/
theorem lineStep_cq (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight)) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (hk : 6 < -2 * I.halfWeight) (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) (hg : (Matrix.GeneralLinearGroup.det gInf).val ≠ 0)
    (q : FinitePlace) (hq : q ≠ placeThree) (p : Nat.Primes)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv q : Nat.Primes) : ℕ) = (p : ℕ)) :
    LineStep I Z gInf q hq (globalOuterLocalRatio (-2 * I.halfWeight) (fourierCoeff h (p : ℕ)) p) := by
  by_cases hpos : 0 < (Matrix.GeneralLinearGroup.det gInf).val
  · exact lineStep_cq_pos I h hh hform hk Z hZ gInf hpos q hq p hv
  · have hneg : (Matrix.GeneralLinearGroup.det gInf).val < 0 := lt_of_le_of_ne (not_lt.1 hpos) hg
    have hRg : 0 < (Matrix.GeneralLinearGroup.det (binaryRationalReal reflectionQ * gInf)).val := by
      simp only [map_mul, Units.val_mul, det_reflectionQ_real]
      linarith
    exact lineStep_neg_of_pos I h hform gInf hneg Z hZ q hq _
      (lineStep_cq_pos I h hh hform hk _ (hZ_reflect Z hZ) _ hRg q hq p hv)

/-- **The global finite integral is the Euler product, unconditionally.** -/
theorem global_integral_euler (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight)) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (hk : 6 < -2 * I.halfWeight) (gInf : BinaryRealGL) (hg : (Matrix.GeneralLinearGroup.det gInf).val ≠ 0)
    (Z : BinaryFiniteGL) (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val) :
    Integrable (globalIntegrand I Z gInf) (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      ∫ z, globalIntegrand I Z gInf z ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det Z)) (expo I) * vhValueFull (-2 * I.halfWeight) h gInf Z *
          (LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) (((-2 * I.halfWeight : ℤ) : ℂ) - 2) /
            LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) (((-2 * I.halfWeight : ℤ) : ℂ) - 1)) :=
  global_integral_euler_of_lineStep I h hh hform hk gInf hg Z hZ fun p =>
    lineStep_cq I h hh hform hk Z hZ gInf hg (embP p) (embP_ne p) p.val
      (congrArg Subtype.val (Equiv.apply_symm_apply (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)) p.val))

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitUncond
