module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.SingleSplit
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitShape
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitTotalG

@[expose] public section


/-!
# Single-place finite integral (route (b), step (4') for `|S| = 1`)

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

For a finite place `v ≠ 3`, the integral of the global integrand over `U_{v}` against the product of
the finite-away-from-3 measures equals the literal local integral over `ℚ_v²` of `shellIntegrandG`
against `finitePadicMeasure v ⊗ finitePadicMeasure v`. The closed form then follows from
`ShellLitTotalG.local_integral_literal_uncondG`.

Steps:

* `globalIntegrand_eq_atPlace`: on `U_{v}`, the global integrand equals the global integrand at the
  point supported at `v` with the same value (fibre comparison via `smooth_fibre_general`);
* `globalIntegrand_eq_shell`: on `U_{v}`, the global integrand equals `shellIntegrandG v` at the
  padic coordinates of `z`;
* `eU`, `eU_prod_mp`: the singleton coordinate `WS {v} ≃ᵐ ℚ_p` is measure preserving from
  `localPi {v}` to `finitePadicMeasure v`;
* `finiteIntegral_single_transfer`: `setIntegral_UregionS` plus the measure-preserving equivalence.
-/

open Classical Matrix PadicInt MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.PointwiseMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinScalar
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.FibreConst
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG (psiV_mem_OS)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitTotal (zp2_or_shell)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalPlane
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwaySplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayStep
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.SingleSplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitTotalG (local_integral_literal_uncondG)
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.SingleFiniteIntegral

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- `psiV` inverts the padic identification of the completion at `v`. -/
theorem psiV_adic (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (u : v.adicCompletion ℚ) :
    psiV v (finiteCompletionPadicAddEquiv v u) = u := by
  show (finiteCompletionPadicEquiv v).symm (finiteCompletionPadicEquiv v u) = u
  exact (finiteCompletionPadicEquiv v).symm_apply_apply u

/-- The completion at `v` as a measurable equivalence with `ℚ_p`. -/
def eMeas (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] :
    v.adicCompletion ℚ ≃ᵐ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] where
  toEquiv := (finiteCompletionPadicAddEquiv v).toAddEquiv.toEquiv
  measurable_toFun := (finiteCompletionPadicAddEquiv v).continuous.measurable
  measurable_invFun := (finiteCompletionPadicAddEquiv v).symm.continuous.measurable

/-- The singleton coordinate at `{v}`, as a measurable equivalence with `ℚ_p`. -/
def eU (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] :
    WS ({v} : Finset FinitePlace) ≃ᵐ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] :=
  (MeasurableEquiv.piUnique (fun p : ({v} : Finset FinitePlace) => p.1.adicCompletion ℚ)).trans
    (eMeas v)

/-- The singleton coordinate pushes `localPi {v}` to `finitePadicMeasure v`. -/
theorem eU_mp (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] :
    MeasurePreserving (eU v) (localPi ({v} : Finset FinitePlace)) (finitePadicMeasure v) := by
  have hU : MeasurePreserving
      (MeasurableEquiv.piUnique (fun p : ({v} : Finset FinitePlace) => p.1.adicCompletion ℚ))
      (localPi ({v} : Finset FinitePlace)) (finiteCompletionMeasure v) :=
    measurePreserving_piUnique (fun p : ({v} : Finset FinitePlace) => finiteCompletionMeasure p.1)
  have hE : MeasurePreserving (eMeas v) (finiteCompletionMeasure v) (finitePadicMeasure v) :=
    ⟨(eMeas v).measurable, rfl⟩
  exact hE.comp hU

/-- The product of the singleton coordinates is measure preserving. -/
theorem eU_prod_mp (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] :
    MeasurePreserving (MeasurableEquiv.prodCongr (eU v) (eU v))
      ((localPi ({v} : Finset FinitePlace)).prod (localPi ({v} : Finset FinitePlace)))
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) :=
  (eU_mp v).prod (eU_mp v)

/-- **Fibre comparison on `U_{v}`.** The global integrand at `z ∈ U_{v}` equals the global integrand
at the point supported at `v` with the same local values. -/
theorem globalIntegrand_eq_atPlace (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] (hv3 : v ≠ placeThree)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL)
    (z : FiniteAwayThree × FiniteAwayThree) (hz : z ∈ UregionS ({v} : Finset FinitePlace)) :
    globalIntegrand I Z gInf z =
      globalIntegrand I Z gInf
        (finiteAwayThreeAtPlace v hv3 (finiteEvaluation v (awayVal z.1)),
          finiteAwayThreeAtPlace v hv3 (finiteEvaluation v (awayVal z.2))) := by
  obtain ⟨P0, κ0, hP20, hP21, hfac, hκ0⟩ :=
    plane_factor_all v (finiteCompletionPadicAddEquiv v (finiteEvaluation v (awayVal z.1)))
      (finiteCompletionPadicAddEquiv v (finiteEvaluation v (awayVal z.2)))
  rw [psiV_adic, psiV_adic] at hfac
  unfold globalIntegrand
  refine smooth_fibre_general I h hform ({v} : Finset FinitePlace)
    (extend1 v P0) (extend1 v κ0) (extend1 v P0) (extend1 v κ0)
    ?_ ?_ (LfinGLof (awayVal z.1) (awayVal z.2))
    (LfinGLof (awayVal (finiteAwayThreeAtPlace v hv3 (finiteEvaluation v (awayVal z.1))))
      (awayVal (finiteAwayThreeAtPlace v hv3 (finiteEvaluation v (awayVal z.2)))))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ Z hZ gInf
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [extend1_self]
    exact ⟨hP20, hP21⟩
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [extend1_self]
    exact ⟨hP20, hP21⟩
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [evM3_LfinGLof, extend1_self, extend1_self]
    exact hfac
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [extend1_self]
    exact hκ0
  · intro w hw
    exact intGL3_LfinGLof_of_mem hz w hw
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [evM3_LfinGLof, eval_atPlace_self, eval_atPlace_self, extend1_self, extend1_self]
    exact hfac
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [extend1_self]
    exact hκ0
  · intro w hw
    exact intGL3_LfinGLof_of_mem (atPlace_mem_UregionS v hv3 _ _) w hw
  · intro w _
    rfl

/-- **Integrand on `U_{v}` in padic coordinates.** For `z ∈ U_{v}` the global integrand is the literal
shell integrand at the `ℚ_v`-coordinates of `z`. -/
theorem globalIntegrand_eq_shell (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] (hv3 : v ≠ placeThree)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL)
    (z : FiniteAwayThree × FiniteAwayThree) (hz : z ∈ UregionS ({v} : Finset FinitePlace)) :
    globalIntegrand I Z gInf z =
      shellIntegrandG v I Z gInf
        (finiteCompletionPadicAddEquiv v (finiteEvaluation v (awayVal z.1)),
          finiteCompletionPadicAddEquiv v (finiteEvaluation v (awayVal z.2))) := by
  have h1 := globalIntegrand_eq_atPlace I h hform v hv3 Z hZ gInf z hz
  have h2 := globalIntegrand_atPlace_eq_shell I h hform v hv3 Z hZ gInf
    (finiteCompletionPadicAddEquiv v (finiteEvaluation v (awayVal z.1)))
    (finiteCompletionPadicAddEquiv v (finiteEvaluation v (awayVal z.2)))
  rw [psiV_adic, psiV_adic] at h2
  rw [h1, h2]

/-- **Transfer of the single-place integral to `ℚ_v²`.** -/
theorem finiteIntegral_single_transfer (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] (hv3 : v ≠ placeThree)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL)
    (hF : AEStronglyMeasurable (shellIntegrandG v I Z gInf)
      ((finitePadicMeasure v).prod (finitePadicMeasure v))) :
    ∫ z in UregionS ({v} : Finset FinitePlace), globalIntegrand I Z gInf z
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      ∫ z, shellIntegrandG v I Z gInf z ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) := by
  have hS : ∀ p ∈ ({v} : Finset FinitePlace), p ≠ placeThree := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact hv3
  have hcongr : ∫ z in UregionS ({v} : Finset FinitePlace), globalIntegrand I Z gInf z
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      ∫ z in UregionS ({v} : Finset FinitePlace),
        (shellIntegrandG v I Z gInf ∘ MeasurableEquiv.prodCongr (eU v) (eU v))
          (piS ({v} : Finset FinitePlace) z.1, piS ({v} : Finset FinitePlace) z.2)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
    apply setIntegral_congr_fun (UregionS_measurable ({v} : Finset FinitePlace) hS)
    intro z hz
    rw [globalIntegrand_eq_shell I h hform v hv3 Z hZ gInf z hz]
    rfl
  have hG : AEStronglyMeasurable
      (shellIntegrandG v I Z gInf ∘ MeasurableEquiv.prodCongr (eU v) (eU v))
      ((localPi ({v} : Finset FinitePlace)).prod (localPi ({v} : Finset FinitePlace))) :=
    hF.comp_measurePreserving (eU_prod_mp v)
  rw [hcongr, setIntegral_UregionS ({v} : Finset FinitePlace) hS _ hG]
  exact (eU_prod_mp v).integral_comp' (shellIntegrandG v I Z gInf)

/-- **Single-place finite integral, closed form.** For a finite place `v ≠ 3` with
`v` the prime `p` of `ℚ_p`, the integral of the global integrand over `U_{v}` equals
`normPower(det g_f) · vhValueFull(g∞, g_f · ι_v gp⁻¹) · c_p`, the constant `c_p` being the one of
`ShellLitTotalG.local_integral_literal_uncondG`. -/
theorem finiteIntegral_single_closed (I : EichlerInput σ n) (k : ℤ)
    (hk_eq : k = -2 * I.halfWeight) (hk : 6 < k)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (p : Nat.Primes) (v : FinitePlace)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (hv3 : v ≠ placeThree) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) gf).val) :
    ∫ z in UregionS ({v} : Finset FinitePlace), globalIntegrand I gf gInf z
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf)) (((k : ℤ) : ℂ) / 2) *
        vhValueFull k h gInf (gf * ιGL v gp⁻¹) *
        ((1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (1 - k) + ((p : ℕ) : ℂ) ^ (1 - k)) /
          (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k))) := by
  subst hk_eq
  obtain ⟨hint, heq⟩ := local_integral_literal_uncondG I _ rfl hk h hh hform p v hv gInf hgInf
    gf gp hgp hgI
  rw [finiteIntegral_single_transfer I h hform v hv3 gf hZ gInf
    (integrableOn_univ.mp hint).aestronglyMeasurable]
  exact heq

end TernaryPeriodPolynomials.Argument.LatticeCounts.SingleFiniteIntegral

end
