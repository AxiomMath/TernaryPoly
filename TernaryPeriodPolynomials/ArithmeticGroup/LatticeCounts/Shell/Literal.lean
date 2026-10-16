module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.SeedCp
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitFibre
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitSet
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.FibreSum

@[expose] public section


/-!
# The literal shell value and the local factor with no seed premise (`0 < det g∞`)

Formalized by Claude Haiku 5.5.

`shellValLit v I g∞ s` is the literal integral of the shell integrand over `pairShell p s`
with respect to the finite-place product Haar measure. Its seed identity is proved from the
fibre decomposition (`ShellLitSet`), fibre constancy (`ShellLitFibre`) and the abstract
fibre-sum integral (`ShellFibreSum`). `shell_total_literal` then applies
`ShellBundle.shell_total_eq_cp` with the seed identity discharged: no seed premise remains.

The hypothesis `6 < k` is explicit, with `k = -2·halfWeight`.
-/

open MeasureTheory Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers (cuspScalarWeightedLinear finitePadicMeasure)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform)
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue (vhValue)
open TernaryPeriodPolynomials.Argument.LatticeCounts.IotaValue (intMat)
open TernaryPeriodPolynomials.Argument.LatticeCounts (cyclicHNF hnfData)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLiteral

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The literal shell value: the integral of the shell integrand over `pairShell p s`
with respect to the finite-place product Haar measure. -/
def shellValLit (v : FinitePlace) (I : EichlerInput σ n) (gInf : BinaryRealGL) (s : ℕ) : ℂ :=
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  ∫ z in Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s,
    ShellLitFibre.shellIntegrand v I gInf z
    ∂((finitePadicMeasure v).prod (finitePadicMeasure v))

/-- **Seed identity for the literal shell value** (`s ≥ 1`, `0 < det g∞`). -/
theorem shellValLit_seed (v : FinitePlace) (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    {s : ℕ} (hs : 1 ≤ s) :
    shellValLit v I gInf s =
      ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
        ∑ t ∈ cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val s,
          ((ShellBundle.fibreWeight v s t : ℝ) : ℂ) *
            vhValue (-2 * I.halfWeight) h gInf (ιGL v (ShellLitFibre.shellB v t)) := by
  have : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  have key := ShellFibreSum.fibre_sum_integral
    ((finitePadicMeasure v).prod (finitePadicMeasure v))
    (T := cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val s)
    (F := fun t => ShellLitSet.shellFibre (Rat.HeightOneSpectrum.primesEquiv v).val s t)
    (c := fun t => ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
        vhValue (-2 * I.halfWeight) h gInf (ιGL v (ShellLitFibre.shellB v t)))
    (f := ShellLitFibre.shellIntegrand v I gInf)
    (ShellLitSet.isOpen_pairShell hs).measurableSet
    (fun t _ => (ShellLitSet.isOpen_shellFibre hs t).measurableSet)
    (fun t _ => ShellLitSet.shellFibre_sub t)
    (fun i hi j hj hij => Set.disjoint_left.2 fun z hzi hzj =>
      hij (ShellLitSet.shellFibre_unique hi hj hzi hzj))
    (fun z hz => by
      obtain ⟨t, ht, hzt⟩ := ShellLitSet.exists_shellFibre hz
      exact Set.mem_iUnion₂.2 ⟨t, ht, hzt⟩)
    (fun t ht => by
      have hm : (finitePadicMeasure v).prod (finitePadicMeasure v)
          (ShellLitSet.shellFibre (Rat.HeightOneSpectrum.primesEquiv v).val s t) =
          ((((Rat.HeightOneSpectrum.primesEquiv v).val ^ s -
            (Rat.HeightOneSpectrum.primesEquiv v).val ^ (s - 1) : ℕ)) : ENNReal) :=
        Padic.hermLat_fibre_measure_finitePlace v hs ht
      rw [hm]
      exact ENNReal.natCast_ne_top _)
    (fun t ht z hz => by
      have hzt : Padic.pairLat (Rat.HeightOneSpectrum.primesEquiv v).val z =
          Padic.hermLat (Rat.HeightOneSpectrum.primesEquiv v).val t :=
        (Submodule.toAddSubgroup_inj _ _).1 hz.2
      exact ShellLitFibre.shellIntegrand_fibre v I h hform gInf hg ht hz.1 hzt
        (ShellLitFibre.shellB v t)
        (fun i j => ShellLitFibre.shellB_entry v (ShellLitSet.mem_hnfData_of_cyclic ht) i j))
  dsimp only [shellValLit]
  rw [key.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hw : ShellBundle.fibreWeight v s t =
      ((finitePadicMeasure v).prod (finitePadicMeasure v)).real
        (ShellLitSet.shellFibre (Rat.HeightOneSpectrum.primesEquiv v).val s t) := rfl
  rw [hw, Complex.real_smul]
  ring

/-- **The local factor with no seed premise (`0 < det g∞`).** The literal shell values are
summable and, with `v_h`, sum to `v_h · c_p`, where `c_p` is the right-hand side of the `unramified_local_factor`. The hypothesis `6 < k` is explicit, with `k = -2·halfWeight`. -/
theorem shell_total_literal (I : EichlerInput σ n) (k : ℤ) (hk_eq : k = -2 * I.halfWeight)
    (hk : 6 < k) (h : CuspForm levelOne k) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (p : Nat.Primes) (v : FinitePlace)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val) :
    Summable (fun r : ℕ => shellValLit v I gInf (r + 1)) ∧
    vhValue k h gInf 1 + ∑' r : ℕ, shellValLit v I gInf (r + 1) =
      vhValue k h gInf 1 * ((1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (1 - k) +
        ((p : ℕ) : ℂ) ^ (1 - k)) /
        (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k))) := by
  subst hk_eq
  have hseed : ∀ s : ℕ, 1 ≤ s → shellValLit v I gInf s =
      (((p.val : ℝ) ^ (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
        ∑ t ∈ cyclicHNF p.val s, ((ShellBundle.fibreWeight v s t : ℝ) : ℂ) *
          vhValue (-2 * I.halfWeight) h gInf (ιGL v (ShellLitFibre.shellB v t)) := by
    intro s hs
    rw [shellValLit_seed v I h hform gInf hgInf hs, hv]
  have hB : ∀ s : ℕ, ∀ t ∈ hnfData (p.val ^ s),
      (ShellLitFibre.shellB v t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ) := by
    intro s t ht
    rw [← hv] at ht
    exact ShellLitFibre.shellB_val v ht
  obtain ⟨hsum, heq⟩ := ShellBundle.shell_total_eq_cp hk h hh p v hv
    (ShellLitFibre.shellB v) hB gInf hgInf (shellValLit v I gInf) hseed
  exact ⟨hsum, heq⟩

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLiteral

end
