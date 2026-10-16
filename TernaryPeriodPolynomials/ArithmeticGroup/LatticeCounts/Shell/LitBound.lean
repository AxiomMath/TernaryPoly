module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitTotal

@[expose] public section


/-!
# Discharge of `habs`: the uniform Hecke bound on the shell integrals

For `0 < det g∞` the value `vhValue k h g∞ gf` is `F_h(γ g∞)` with `γ ∈ GL₂⁺(ℚ)`, and
`|F_h(g)| = Im(g i)^{k/2} |h(g i)|` for `det g > 0`. The cusp-form bound
`CuspFormClass.exists_bound` gives `Im^{k/2} |h| ≤ C`, so `|F_h| ≤ C` uniformly.
On the shell `pairShell p s` the integrand is `p^{-s k/2}` times such a value
(`ShellLitFibre.shellIntegrand_fibre`), and the shell has measure `(1 - p⁻²) p^{2s}`
(`Padic.shell_measure_prod_rat`). So the shell integral of the norm is at most
`C p^{-s k/2} p^{2s}`, which is summable in `s` for `k > 6`. No Ramanujan input is used.
This removes the hypothesis `habs` of `ShellLitTotal.local_integral_literal`.
-/

open MeasureTheory Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (cuspScalarWeightedLinear finitePadicMeasure finitePadicMeasure_normalized)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform)
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue (vhValue)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary (Nf Fh)
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction (binaryRationalReal)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBound

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- For `det g > 0`, `‖Nf k g‖ = Im(g i)^{k/2}`. -/
theorem norm_Nf_eq (k : ℤ) (g : GL (Fin 2) ℝ) (hg : 0 < (Matrix.GeneralLinearGroup.det g).val) :
    ‖Nf k g‖ = (g • UpperHalfPlane.I).im ^ ((k : ℝ) / 2) := by
  have hd : (0 : ℝ) < (Matrix.GeneralLinearGroup.det g).val := by exact_mod_cast hg
  have hn : 0 < ‖UpperHalfPlane.denom g Complex.I‖ :=
    norm_pos_iff.2 (UpperHalfPlane.denom_ne_zero_of_im g (by simp))
  have him : (g • UpperHalfPlane.I).im =
      (Matrix.GeneralLinearGroup.det g).val / ‖UpperHalfPlane.denom g Complex.I‖ ^ 2 := by
    rw [UpperHalfPlane.im_smul_eq_div_normSq, abs_of_pos hd, Complex.normSq_eq_norm_sq,
      UpperHalfPlane.I_im, mul_one]
    rfl
  have hre : ((k : ℂ) / 2).re = (k : ℝ) / 2 := by
    simp
  have hpow : (‖UpperHalfPlane.denom g Complex.I‖ ^ 2) ^ ((k : ℝ) / 2) =
      ‖UpperHalfPlane.denom g Complex.I‖ ^ (k : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    push_cast
    ring
  unfold Nf
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hd, hre, norm_zpow, him,
    Real.div_rpow hd.le (by positivity), hpow, _root_.zpow_neg, ← Real.rpow_intCast]
  ring

/-- Uniform bound: `‖F_h(g)‖ ≤ C` for all `g` with `det g > 0`, from the cusp-form bound. -/
theorem norm_Fh_le (k : ℤ) (h : CuspForm levelOne k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GL (Fin 2) ℝ, 0 < (Matrix.GeneralLinearGroup.det g).val →
      ‖Fh k ⇑h g‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (k := k) (Γ := levelOne) h
  refine ⟨max C 0, le_max_right _ _, fun g hg => ?_⟩
  have hτ : 0 < (g • UpperHalfPlane.I).im := (g • UpperHalfPlane.I).im_pos
  have hpos : 0 < (g • UpperHalfPlane.I).im ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hτ _
  have hbd := hC (g • UpperHalfPlane.I)
  unfold Fh
  rw [norm_mul, norm_Nf_eq k g hg]
  calc _ ≤ (g • UpperHalfPlane.I).im ^ ((k : ℝ) / 2) *
        (C / (g • UpperHalfPlane.I).im ^ ((k : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hbd hpos.le
    _ = C := by field_simp
    _ ≤ max C 0 := le_max_left _ _

theorem det_binaryRationalReal_val (γ : BinaryRationalGL) :
    (Matrix.GeneralLinearGroup.det (binaryRationalReal γ)).val =
      ((Matrix.GeneralLinearGroup.det γ).val : ℝ) := by
  simp [binaryRationalReal, Matrix.GeneralLinearGroup.det, GeneralLinearGroup.map]
  exact (RingHom.map_det (Rat.castHom ℝ) _).symm

/-- The model value is bounded by the uniform `F_h` bound when `det g∞ > 0`. -/
theorem norm_vhValue_le (k : ℤ) (h : CuspForm levelOne k) (C : ℝ)
    (hC : ∀ g : GL (Fin 2) ℝ, 0 < (Matrix.GeneralLinearGroup.det g).val → ‖Fh k ⇑h g‖ ≤ C)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) :
    ‖vhValue k h gInf gf‖ ≤ C := by
  unfold vhValue
  apply hC
  have hγ := (Classical.choice
    (TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof.latticeReductionExists
      gf)).det_pos
  rw [map_mul, Units.val_mul, det_binaryRationalReal_val]
  exact mul_pos (by exact_mod_cast hγ) hg

/-- Pointwise bound of the literal shell integrand on the shell `pairShell p s`. -/
theorem norm_shellIntegrand_le (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n) (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    {C : ℝ}
    (hC : ∀ g : GL (Fin 2) ℝ, 0 < (Matrix.GeneralLinearGroup.det g).val →
      ‖Fh (-2 * I.halfWeight) ⇑h g‖ ≤ C)
    {s : ℕ} {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hz : z ∈ Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s) :
    ‖ShellLitFibre.shellIntegrand v I gInf z‖ ≤
      ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) * C := by
  obtain ⟨t, ht, hzt⟩ := ShellLitSet.exists_shellFibre hz
  have hzt' : Padic.pairLat (Rat.HeightOneSpectrum.primesEquiv v).val z =
      Padic.hermLat (Rat.HeightOneSpectrum.primesEquiv v).val t :=
    (Submodule.toAddSubgroup_inj _ _).1 hzt.2
  rw [ShellLitFibre.shellIntegrand_fibre v I h hform gInf hg ht hz hzt' (ShellLitFibre.shellB v t)
    (fun i j => ShellLitFibre.shellB_entry v (ShellLitSet.mem_hnfData_of_cyclic ht) i j),
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact mul_le_mul_of_nonneg_left (norm_vhValue_le _ h C hC gInf hg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The shell integral of the norm is at most `p^{-s k/2} C · μ(shell)`, with `μ(shell) ≤ p^{2s}`. -/
theorem shell_integral_norm_le (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n) (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ g : GL (Fin 2) ℝ, 0 < (Matrix.GeneralLinearGroup.det g).val →
      ‖Fh (-2 * I.halfWeight) ⇑h g‖ ≤ C)
    {s : ℕ} (hs : 1 ≤ s) :
    ∫ z in Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s,
        ‖ShellLitFibre.shellIntegrand v I gInf z‖
          ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) ≤
      ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) * C *
        ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * s) := by
  have hpr := (inferInstance : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime).out
  have hp1 : (1 : ℝ) ≤ ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) :=
    (Nat.one_lt_cast.2 hpr.one_lt).le
  have hS : MeasurableSet (Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s) :=
    (ShellLitSet.isOpen_pairShell hs).measurableSet
  have hmeas := Padic.shell_measure_prod_rat (Rat.HeightOneSpectrum.primesEquiv v).val
    (μ₁ := finitePadicMeasure v) (finitePadicMeasure_normalized v) hs
  have hfin : ((finitePadicMeasure v).prod (finitePadicMeasure v))
      (Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s) ≠ ⊤ := by
    rw [hmeas]
    exact ENNReal.ofReal_ne_top
  have hc0 : 0 ≤ ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
      (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) * C :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hC0
  have hle : ∀ z ∈ Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s,
      ‖ShellLitFibre.shellIntegrand v I gInf z‖ ≤
        ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) * C :=
    fun z hz => norm_shellIntegrand_le v I h hform gInf hg hC hz
  have hP : (0 : ℝ) ≤ ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * s) :=
    pow_nonneg (by linarith) _
  have hx : (0 : ℝ) ≤ (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ 2)⁻¹ := by positivity
  have hnonneg : (0 : ℝ) ≤ (1 - (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ 2)⁻¹) *
      ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * s) := by
    apply mul_nonneg _ hP
    have : (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ hp1)
    linarith
  calc _ ≤ ∫ z in Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s,
        (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) * C) ∂((finitePadicMeasure v).prod
            (finitePadicMeasure v)) :=
        setIntegral_mono_on (ShellLitTotal.shell_integrableOn v I h hform gInf hg hs).norm
          (integrableOn_const hfin) hS hle
    _ = (1 - (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ 2)⁻¹) *
          ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * s) *
          (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
            (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) * C) := by
        rw [setIntegral_const, Measure.real, hmeas, ENNReal.toReal_ofReal hnonneg, smul_eq_mul]
    _ ≤ ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * s) *
          (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
            (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) * C) := by
        nlinarith [mul_nonneg (mul_nonneg hx hP) hc0]
    _ = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) * C *
        ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * s) := by ring

/-- **The shell sum is summable for `k > 6` (this discharges `habs`).** -/
theorem summable_shell_norm (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n) (h : CuspForm levelOne (-2 * I.halfWeight))
    (hk : 6 < -2 * I.halfWeight)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val) :
    Summable (fun r : ℕ => ∫ z in Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1),
      ‖ShellLitFibre.shellIntegrand v I gInf z‖
        ∂((finitePadicMeasure v).prod (finitePadicMeasure v))) := by
  obtain ⟨C, hC0, hC⟩ := norm_Fh_le (-2 * I.halfWeight) h
  have hpr := (inferInstance : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime).out
  have hp1 : (1 : ℝ) < ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) :=
    Nat.one_lt_cast.2 hpr.one_lt
  have hp0 : (0 : ℝ) < ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
      ((2 : ℝ) - (((-2 * I.halfWeight : ℤ) : ℝ)) / 2) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := hq ▸ Real.rpow_nonneg hp0.le _
  have hk' : (6 : ℝ) < ((-2 * I.halfWeight : ℤ) : ℝ) := by exact_mod_cast hk
  have hq1 : q < 1 := by
    rw [hq]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  refine Summable.of_nonneg_of_le (fun r => integral_nonneg fun z => norm_nonneg _)
    (fun r => ?_) ((summable_geometric_of_lt_one hq0 hq1).mul_left (C * q))
  have hb := shell_integral_norm_le v I h hform gInf hg hC0 hC (s := r + 1) (by omega)
  refine hb.trans (le_of_eq ?_)
  have key : ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
      (-(((r + 1 : ℕ) : ℝ)) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) *
        ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * (r + 1)) = q ^ (r + 1) := by
    rw [hq, ← Real.rpow_natCast (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
      ((2 : ℝ) - (((-2 * I.halfWeight : ℤ) : ℝ)) / 2)) (r + 1), ← Real.rpow_mul hp0.le,
      ← Real.rpow_natCast ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) (2 * (r + 1)),
      ← Real.rpow_add hp0]
    congr 1
    push_cast
    ring
  calc _ = C * (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(((r + 1 : ℕ) : ℝ)) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) *
        ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * (r + 1))) := by ring
    _ = C * q ^ (r + 1) := by rw [key]
    _ = C * q * q ^ r := by ring

/-- **The whole literal local integral over `ℚ_p²` (`0 < det g∞`), unconditionally.**
Same conclusion as `ShellLitTotal.local_integral_literal`, with `habs` proved above. -/
theorem local_integral_literal_uncond (I : EichlerInput σ n) (k : ℤ) (hk_eq : k = -2 * I.halfWeight)
    (hk : 6 < k) (h : CuspForm levelOne k) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (p : Nat.Primes) (v : FinitePlace)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] :
    IntegrableOn (ShellLitFibre.shellIntegrand v I gInf) Set.univ
        ((finitePadicMeasure v).prod (finitePadicMeasure v)) ∧
      ∫ z, ShellLitFibre.shellIntegrand v I gInf z
          ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) =
        vhValue k h gInf 1 * ((1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (1 - k) +
          ((p : ℕ) : ℂ) ^ (1 - k)) /
          (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k))) := by
  subst hk_eq
  exact ShellLitTotal.local_integral_literal I (-2 * I.halfWeight) rfl hk h hh hform p v hv
    gInf hgInf (summable_shell_norm v I h hk hform gInf hgInf)

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBound
