module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitTotalG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitNegG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitNegFull

@[expose] public section


/-!
# The whole literal local integral over `ℚ_p²` at a general base point, for every `det g∞ ≠ 0`

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

Generalises `ShellLitNegFull.local_integral_literal_full` (base point `g_f = 1`) to an arbitrary finite
base point `g_f`, with `gf.val.map (finiteEvaluation v) = gp.val` and `IntGL v gp.val` as explicit hypotheses.

For `det g∞ > 0` this is `ShellLitTotalG.local_integral_literal_uncondG`. For `det g∞ < 0` the sign change
`σ(z₁, z₂) = (z₁, -z₂)` preserves `μ ⊗ μ` (`ShellLitNegFull.sigma_measurePreserving`), and the pointwise sign
identity `ShellLitNegG.shellIntegrandG_neg` moves the integral to the positive-determinant base point
`(R g_f R, R g∞)`, with local component `R gp R`. The normalising factor is unchanged, since
`det (R g_f R) = det g_f`, and `vhValueFull g∞ (g_f ι_v gp⁻¹) = vhValueFull (R g∞) ((R g_f R) ι_v (R gp R)⁻¹)`
by `vhValueNeg_eq_conj`.
-/

open MeasureTheory Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction (EichlerInput)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (finitePadicMeasure cuspScalarWeightedLinear)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
  (reflectionGL reflectionQ det_reflectionQ_real vhValueFull)
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
  (binaryRationalReal binaryRationalFinite)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegConj
  (vhValueNeg_eq_conj conj_ιGL qv_reflection evM_map_rat)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic (IntGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof (evM)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG (shellIntegrandG)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitTotalG
  (local_integral_literal_uncondG)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegFull
  (sigmaEquiv sigma_measurePreserving integrable_sigma_iff)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegG
  (shellIntegrandG_neg det_reflect_base reflectionF_mul_self)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegFullG

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- Conjugation by `R = diag(1,-1)` in `GL₂(𝔸_f)` is multiplicative on products: `R(ab)R = (RaR)(RbR)`. -/
theorem conj_mul (Rf a b : BinaryFiniteGL) (hRR : Rf * Rf = 1) :
    Rf * (a * b) * Rf = (Rf * a * Rf) * (Rf * b * Rf) := by
  have hc : ∀ x : BinaryFiniteGL, Rf * (Rf * x) = x := fun x => by
    rw [← mul_assoc, hRR, one_mul]
  simp only [mul_assoc, hc]

/-- The inverse of the reflected local element: `(R gp R)⁻¹ = R gp⁻¹ R`. -/
theorem inv_conj (v : FinitePlace) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    (reflectionGL (v.adicCompletion ℚ) * gp * reflectionGL (v.adicCompletion ℚ))⁻¹ =
      reflectionGL (v.adicCompletion ℚ) * gp⁻¹ * reflectionGL (v.adicCompletion ℚ) := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev,
    inv_eq_of_mul_eq_one_right (ShellLitNegG.reflectionGL_mul_self (v.adicCompletion ℚ)), mul_assoc]

/-- **The whole literal local integral over `ℚ_p²`, at a general base point, for every `det g∞ ≠ 0`.**
Integrable on `ℚ_p²`, and the integral is `normPower(det g_f) b · vhValueFull(g∞, g_f · ι_v gp⁻¹) · c_p`. -/
theorem local_integral_literal_fullG (I : EichlerInput σ n) (k : ℤ) (hk_eq : k = -2 * I.halfWeight)
    (hk : 6 < k) (h : CuspForm levelOne k) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (p : Nat.Primes) (v : FinitePlace)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (gInf : BinaryRealGL) (hgInf : (Matrix.GeneralLinearGroup.det gInf).val ≠ 0)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val) :
    IntegrableOn (shellIntegrandG v I gf gInf) Set.univ
        ((finitePadicMeasure v).prod (finitePadicMeasure v)) ∧
      ∫ z, shellIntegrandG v I gf gInf z ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) =
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf)) (((k : ℤ) : ℂ) / 2) *
          vhValueFull k h gInf (gf * ιGL v gp⁻¹) *
        ((1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (1 - k) +
          ((p : ℕ) : ℂ) ^ (1 - k)) /
          (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k))) := by
  subst hk_eq
  rcases lt_or_gt_of_ne hgInf with hneg | hpos
  · have hRg : 0 < (Matrix.GeneralLinearGroup.det (binaryRationalReal reflectionQ * gInf)).val := by
      simp only [map_mul, Units.val_mul, det_reflectionQ_real]
      linarith
    have hRf : (binaryRationalFinite reflectionQ).val.map (finiteEvaluation v) =
        (reflectionGL (v.adicCompletion ℚ)).val := by
      show evM v (reflectionQ.val.map (algebraMap ℚ FiniteAdeles)) = _
      rw [evM_map_rat, qv_reflection]
    have hgp' : (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ).val.map
        (finiteEvaluation v) =
        (reflectionGL (v.adicCompletion ℚ) * gp * reflectionGL (v.adicCompletion ℚ)).val := by
      simp only [Units.val_mul, Matrix.map_mul, hRf, hgp]
    have hgI' : IntGL v (reflectionGL (v.adicCompletion ℚ) * gp * reflectionGL (v.adicCompletion ℚ)).val := by
      rw [Units.val_mul, Units.val_mul]
      exact ShellLitNegG.intGL_reflect v gp.val hgI
    obtain ⟨hI, hint⟩ := local_integral_literal_uncondG I (-2 * I.halfWeight) rfl hk h hh hform p v hv
      (binaryRationalReal reflectionQ * gInf) hRg
      (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ)
      (reflectionGL (v.adicCompletion ℚ) * gp * reflectionGL (v.adicCompletion ℚ)) hgp' hgI'
    have hpt : ∀ z, shellIntegrandG v I gf gInf z =
        shellIntegrandG v I (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ)
          (binaryRationalReal reflectionQ * gInf) (sigmaEquiv v z) := fun z =>
      shellIntegrandG_neg v I h hform gInf hneg gf gp hgp hgI z
    have hfun : shellIntegrandG v I gf gInf =
        shellIntegrandG v I (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ)
          (binaryRationalReal reflectionQ * gInf) ∘ sigmaEquiv v :=
      funext hpt
    have hIntg : IntegrableOn (shellIntegrandG v I gf gInf) Set.univ
        ((finitePadicMeasure v).prod (finitePadicMeasure v)) := by
      rw [integrableOn_univ, hfun]
      exact (integrable_sigma_iff v _).2 (integrableOn_univ.1 hI)
    have hintEq : ∫ z, shellIntegrandG v I gf gInf z ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) =
        ∫ z, shellIntegrandG v I (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ)
          (binaryRationalReal reflectionQ * gInf) z ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) := by
      calc ∫ z, shellIntegrandG v I gf gInf z ∂((finitePadicMeasure v).prod (finitePadicMeasure v))
          = ∫ z, shellIntegrandG v I (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ)
              (binaryRationalReal reflectionQ * gInf) (sigmaEquiv v z)
              ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun z => hpt z
        _ = ∫ z, shellIntegrandG v I (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ)
              (binaryRationalReal reflectionQ * gInf) z ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) :=
            MeasurePreserving.integral_comp' (sigma_measurePreserving v)
              (fun y => shellIntegrandG v I (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ)
                (binaryRationalReal reflectionQ * gInf) y)
    -- The value identity: `vhValueFull` at `(g∞, g_f ι gp⁻¹)` equals `vhValueFull` at the reflected
    -- point `(R g∞, (R g_f R) ι (R gp R)⁻¹)`, by `vhValueNeg_eq_conj`.
    have hval : vhValueFull (-2 * I.halfWeight) h gInf (gf * ιGL v gp⁻¹) =
        vhValueFull (-2 * I.halfWeight) h (binaryRationalReal reflectionQ * gInf)
          ((binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ) *
            ιGL v ((reflectionGL (v.adicCompletion ℚ) * gp * reflectionGL (v.adicCompletion ℚ))⁻¹)) := by
      unfold vhValueFull
      rw [ite_eq_right (not_lt.2 hneg.le), ite_eq_left hRg,
        vhValueNeg_eq_conj _ h gInf hneg (gf * ιGL v gp⁻¹),
        conj_mul (binaryRationalFinite reflectionQ) gf (ιGL v gp⁻¹) reflectionF_mul_self,
        conj_ιGL v gp⁻¹, inv_conj v gp]
    refine ⟨hIntg, ?_⟩
    rw [hintEq, hint, det_reflect_base gf, hval]
  · exact local_integral_literal_uncondG I (-2 * I.halfWeight) rfl hk h hh hform p v hv gInf hpos gf gp hgp hgI

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegFullG

end
