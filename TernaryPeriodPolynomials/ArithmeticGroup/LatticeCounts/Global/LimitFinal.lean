module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitIntegrable
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.OuterLimit

@[expose] public section


/-!
# Global limit: the global finite integral as the outer Euler ratio

`FiniteIdentity I h Z gInf v` is the finite-`S` formula (4'), stated as a named proposition: for every finite set `T` of primes `≠ 3`,
`∫_{U_T} F = v · ∏_{p∈T} c_p` with `c_p = globalOuterLocalRatio`.  `global_integral_eq_outer_ratio'` derives, for `k > 6`, that `F` is integrable on `FiniteAwayThree²` and
`∫ F = v · L^{(3)}(h,k-2) / L^{(3)}(h,k-1)`, from `FiniteIdentity` (a hypothesis here, to be discharged by H4's finite-`S` theorem), the integrability/convergence of
`GlobalLimitIntegrable` and `GlobalOuterLimit.global_integral_eq_outer_ratio`.

The archimedean point `g∞` is any element of `GL₂(ℝ)` with `det g∞ ≠ 0`: the paper defines `v_h` on `GL₂⁺(ℝ)` and "reflections supply the other real component"; `vhValueFull` does this (`vhValueNeg`), and the uniform bound for `det < 0` is `GlobalLimitPointwise.norm_vhValueFull_le_ne`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Filter Topology Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitExhaust
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitIntegrable

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitFinal

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- **The finite-`S` formula (4')** as a proposition: the integral of the global integrand over `U_T` is `v` times the product of the local ratios over `T`. -/
def FiniteIdentity (I : EichlerInput σ n) (h : CuspForm levelOne (-2 * I.halfWeight)) (Z : BinaryFiniteGL)
    (gInf : BinaryRealGL) (v : ℂ) : Prop :=
  ∀ T : Finset PIdx,
    ∫ z in Uex T, globalIntegrand I Z gInf z ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      v * ∏ p ∈ T, globalOuterLocalRatio (-2 * I.halfWeight) (fourierCoeff h p.val.val) p.val

/-- **The global finite integral as the outer Euler ratio**, from the finite-`S` formula. -/
theorem global_integral_eq_outer_ratio' (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight)) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (hk : 6 < -2 * I.halfWeight) (gInf : BinaryRealGL) (hg : (Matrix.GeneralLinearGroup.det gInf).val ≠ 0)
    (Z : BinaryFiniteGL) (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (v : ℂ) (hfin : FiniteIdentity I h Z gInf v) :
    Integrable (globalIntegrand I Z gInf) (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      ∫ z, globalIntegrand I Z gInf z ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
        v * (LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) (((-2 * I.halfWeight : ℤ) : ℂ) - 2) /
          LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) (((-2 * I.halfWeight : ℤ) : ℂ) - 1)) := by
  obtain ⟨hint, hlim⟩ := globalIntegrand_integrable_tendsto I h hform hk gInf hg Z hZ
  exact ⟨hint, global_integral_eq_outer_ratio hk h hh v _ (fun T => ∫ z in Uex T, globalIntegrand I Z gInf z
    ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) hfin hlim⟩

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitFinal
