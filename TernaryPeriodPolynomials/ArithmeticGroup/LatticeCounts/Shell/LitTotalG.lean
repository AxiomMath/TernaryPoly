module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LiteralG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBoundG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitZp2G
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitTotal

@[expose] public section


/-!
# The whole literal local integral over `ℚ_p²` at a general base point (`0 < det g∞`)

Formalized by Claude Haiku 5.5.

Generalises `ShellLitTotal.local_integral_literal` to a finite base point `g_f`, with
`gf.val.map (finiteEvaluation v) = gp.val` and `IntGL v gp.val` as explicit hypotheses. The shell
summability hypothesis `habs` of the base-one version is discharged by `ShellLitBoundG.summable_shell_norm_G`.
The integral over `ℚ_p² = ℤ_p² ⊔ ⋃_{s≥1} pairShell s` is the `ℤ_p²` term plus the shell total
`ShellLiteralG.shell_total_literalG`.
-/

open MeasureTheory Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (finitePadicMeasure finitePadicMeasure_normalized cuspScalarWeightedLinear)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic (IntGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg (vhValueFull)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG (shellIntegrandG)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitTotalG

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- **The whole literal local integral over `ℚ_p²` at a general base point (`0 < det g∞`).** The
integrand is integrable on `ℚ_p²`, and its integral is `normPower(det g_f) b · vhValueFull(g∞, g_f · ι_v gp⁻¹)
· c_p`. The shell summability is `ShellLitBoundG.summable_shell_norm_G`. -/
theorem local_integral_literal_uncondG (I : EichlerInput σ n) (k : ℤ) (hk_eq : k = -2 * I.halfWeight)
    (hk : 6 < k) (h : CuspForm levelOne k) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (p : Nat.Primes) (v : FinitePlace)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
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
  obtain ⟨-, heq⟩ := ShellLiteralG.shell_total_literalG I (-2 * I.halfWeight) rfl hk h hh hform p v hv
    gInf hgInf gf gp hgp hgI
  have hZ := ShellLitZp2G.integral_zp2_literal_G v I h hform gInf gf gp hgp hgI
  have hmeasZ : MeasurableSet (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) :=
    (ShellLitSet.isOpen_zp2 (p := (Rat.HeightOneSpectrum.primesEquiv v).val)).measurableSet
  have hmeasS : ∀ r : ℕ, MeasurableSet
      (Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1)) :=
    fun r => (ShellLitSet.isOpen_pairShell (by omega : 1 ≤ r + 1)).measurableSet
  have hi : ∀ r : ℕ, IntegrableOn (shellIntegrandG v I gf gInf)
      (Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1))
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) :=
    fun r => ShellLitBoundG.shell_integrableOn_G v I h hform gInf hgInf gf gp hgp hgI
      (by omega : 1 ≤ r + 1)
  have habs := ShellLitBoundG.summable_shell_norm_G v I h hk hform gInf hgInf gf gp hgp hgI
  have hU : IntegrableOn (shellIntegrandG v I gf gInf)
      (⋃ r : ℕ, Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1))
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) :=
    integrableOn_iUnion_of_summable_integral_norm hi habs
  have hfin : ((finitePadicMeasure v).prod (finitePadicMeasure v))
      (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) ≠ ⊤ := by
    have hnorm := finitePadicMeasure_normalized v
    rw [show Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val =
        {value | ‖value‖ ≤ 1} ×ˢ {value | ‖value‖ ≤ 1} from rfl,
      Measure.prod_prod, hnorm, one_mul]
    exact ENNReal.one_ne_top
  have hZi : IntegrableOn (shellIntegrandG v I gf gInf)
      (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val)
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) :=
    (integrableOn_const (C := normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
        (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
          vhValueFull (-2 * I.halfWeight) h gInf (gf * ιGL v gp⁻¹)) hfin).congr_fun
      (fun z hz => (ShellLitZp2G.shellIntegrandG_zp2 v I h hform gInf gf gp hgp hgI hz).symm) hmeasZ
  have hcov : (Set.univ : Set (ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])) =
      Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val ∪
        ⋃ r : ℕ, Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1) := by
    ext z
    simp only [Set.mem_univ, Set.mem_union, Set.mem_iUnion, true_iff]
    exact ShellLitTotal.zp2_or_shell z
  have hint : IntegrableOn (shellIntegrandG v I gf gInf) Set.univ
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) := by
    rw [hcov]
    exact hZi.union hU
  refine ⟨hint, ?_⟩
  have hdisj : Disjoint (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val)
      (⋃ r : ℕ, Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1)) :=
    Set.disjoint_iUnion_right.2 fun r => ShellLitTotal.zp2_disjoint_shell r
  rw [hZ, mul_div_assoc] at heq
  rw [← setIntegral_univ, hcov, setIntegral_union hdisj (MeasurableSet.iUnion hmeasS) hZi hU,
    integral_iUnion hmeasS ShellLitTotal.shell_pairwise_disjoint hU, hZ]
  exact heq

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitTotalG

end
