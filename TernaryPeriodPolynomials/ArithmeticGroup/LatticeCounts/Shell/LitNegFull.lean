module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBound
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitNegPoint

@[expose] public section


/-!
# The literal local integral over `ℚ_p²` for every `det g∞ ≠ 0`

Formalized by Claude Haiku 5.5.

The sign change `σ(z₁, z₂) = (z₁, -z₂)` preserves the product measure `μ ⊗ μ` on `ℚ_p²`, because
negation preserves the additive Haar measure `μ` of `ℚ_p` (it is inner regular, hence
negation invariant). For `det g∞ < 0`, the pointwise identity `shellIntegrand g∞ = shellIntegrand (R g∞) ∘ σ`
(`ShellLitNegPoint.shellIntegrand_neg`) transfers integrability and the integral from the
positive-determinant value at `R g∞` (`ShellLitBound.local_integral_literal_uncond`). The value at
`R g∞` with `gf = 1` equals `vhValueFull g∞ 1` by `vhValueNeg_eq_conj`.
-/

open MeasureTheory Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction (EichlerInput)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (finitePadicMeasure cuspScalarWeightedLinear)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform)
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue (vhValue)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
  (reflectionQ det_reflectionQ_real vhValueFull)
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
  (binaryRationalFinite binaryRationalReal)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegConj
  (vhValueNeg_eq_conj reflectionQ_mul_self_GL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegPoint (shellIntegrand_neg)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegFull

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- Negation preserves the finite Haar measure on `ℚ_p`. -/
theorem measurePreserving_neg_finite (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] :
    MeasurePreserving (fun x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] => -x)
      (finitePadicMeasure v) (finitePadicMeasure v) :=
  Measure.measurePreserving_neg (finitePadicMeasure v)

/-- The sign change `σ(z₁, z₂) = (z₁, -z₂)` as a measurable equivalence of `ℚ_p²`. -/
def sigmaEquiv (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] :
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ≃ᵐ
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
    (MeasurableEquiv.neg ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])

/-- The product measure `μ ⊗ μ` is invariant under `σ`. -/
theorem sigma_measurePreserving (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] :
    MeasurePreserving (sigmaEquiv v) ((finitePadicMeasure v).prod (finitePadicMeasure v))
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) :=
  MeasurePreserving.prod (MeasurePreserving.id (finitePadicMeasure v))
    (measurePreserving_neg_finite v)

/-- Integrability transfers along `σ`. -/
theorem integrable_sigma_iff (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (F : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] → ℂ) :
    Integrable (F ∘ sigmaEquiv v) ((finitePadicMeasure v).prod (finitePadicMeasure v)) ↔
      Integrable F ((finitePadicMeasure v).prod (finitePadicMeasure v)) :=
  (sigma_measurePreserving v).integrable_comp_emb (sigmaEquiv v).measurableEmbedding

/-- **The whole literal local integral over `ℚ_p²`, for every `det g∞ ≠ 0`.** For `0 < det g∞` this is
`ShellLitBound.local_integral_literal_uncond`; for `det g∞ < 0` it is transported along `σ` from
`R g∞`. -/
theorem local_integral_literal_full (I : EichlerInput σ n) (k : ℤ) (hk_eq : k = -2 * I.halfWeight)
    (hk : 6 < k) (h : CuspForm levelOne k) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (p : Nat.Primes) (v : FinitePlace)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (gInf : BinaryRealGL) (hgInf : (Matrix.GeneralLinearGroup.det gInf).val ≠ 0)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] :
    IntegrableOn (ShellLitFibre.shellIntegrand v I gInf) Set.univ
        ((finitePadicMeasure v).prod (finitePadicMeasure v)) ∧
      ∫ z, ShellLitFibre.shellIntegrand v I gInf z
          ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) =
        vhValueFull k h gInf 1 * ((1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (1 - k) +
          ((p : ℕ) : ℂ) ^ (1 - k)) /
          (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k))) := by
  subst hk_eq
  rcases lt_or_gt_of_ne hgInf with hneg | hpos
  · have hRg : 0 < (Matrix.GeneralLinearGroup.det (binaryRationalReal reflectionQ * gInf)).val := by
      simp only [map_mul, Units.val_mul, det_reflectionQ_real]
      linarith
    obtain ⟨hI, hint⟩ := ShellLitBound.local_integral_literal_uncond I (-2 * I.halfWeight) rfl hk h hh
      hform p v hv (binaryRationalReal reflectionQ * gInf) hRg
    have hfun : ShellLitFibre.shellIntegrand v I gInf =
        ShellLitFibre.shellIntegrand v I (binaryRationalReal reflectionQ * gInf) ∘ sigmaEquiv v :=
      funext fun z => shellIntegrand_neg v I h hform gInf hneg z
    have hone : binaryRationalFinite reflectionQ * (1 : BinaryFiniteGL) *
        binaryRationalFinite reflectionQ = 1 := by
      rw [mul_one, ← map_mul, reflectionQ_mul_self_GL, map_one]
    have hVal : vhValue (-2 * I.halfWeight) h (binaryRationalReal reflectionQ * gInf) 1 =
        vhValueFull (-2 * I.halfWeight) h gInf 1 := by
      rw [vhValueFull, ite_eq_right (not_lt.2 hneg.le), vhValueNeg_eq_conj _ h gInf hneg 1, hone]
    have hIntg : IntegrableOn (ShellLitFibre.shellIntegrand v I gInf) Set.univ
        ((finitePadicMeasure v).prod (finitePadicMeasure v)) := by
      rw [integrableOn_univ, hfun]
      exact (integrable_sigma_iff v _).2 (integrableOn_univ.1 hI)
    have hintEq : ∫ z, ShellLitFibre.shellIntegrand v I gInf z
        ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) =
        ∫ z, ShellLitFibre.shellIntegrand v I (binaryRationalReal reflectionQ * gInf) z
          ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) := by
      calc ∫ z, ShellLitFibre.shellIntegrand v I gInf z
            ∂((finitePadicMeasure v).prod (finitePadicMeasure v))
          = ∫ z, ShellLitFibre.shellIntegrand v I (binaryRationalReal reflectionQ * gInf)
              (sigmaEquiv v z) ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun z => shellIntegrand_neg v I h hform gInf hneg z
        _ = ∫ z, ShellLitFibre.shellIntegrand v I (binaryRationalReal reflectionQ * gInf) z
              ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) :=
            MeasurePreserving.integral_comp' (sigma_measurePreserving v)
              (fun y => ShellLitFibre.shellIntegrand v I (binaryRationalReal reflectionQ * gInf) y)
    refine ⟨hIntg, ?_⟩
    rw [hintEq, hint, hVal]
  · obtain ⟨hI, hint⟩ := ShellLitBound.local_integral_literal_uncond I (-2 * I.halfWeight) rfl hk h hh
      hform p v hv gInf hpos
    refine ⟨hI, ?_⟩
    rw [hint, vhValueFull, ite_eq_left hpos]

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegFull

end
