module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitFibreG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBound
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.FibreSum
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitFibre
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitSet

@[expose] public section


/-!
# Uniform Hecke bound on the shell integrals at a general base point (`g_f`)

Formalized by Claude Haiku 5.5.

Generalises `ShellLitBound` to a base point `g_f` (with `gf.val.map (finiteEvaluation v) = gp.val`
and `IntGL v gp.val` as explicit hypotheses). On `pairShell p s` the literal integrand at `g_f` is
`p^{-s k/2} · normPower(det g_f) b · vhValueFull k h g∞ (ι_v B · (g_f · ι_v gp⁻¹))`
(`shellIntegrandG_fibre`). The factor `normPower(det g_f) b` does not depend on `z`, and
`vhValueFull` is bounded uniformly by the cusp-form bound (`ShellLitBound.norm_Fh_le`). So the shell
integrals of the norm are bounded by `C' · p^{-s k/2} · p^{2s}` with `C' = ‖normPower(det g_f) b‖ · C`,
which is summable in `s` for `k > 6`. No Ramanujan input is used.
-/

open MeasureTheory Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (cuspScalarWeightedLinear finitePadicMeasure finitePadicMeasure_normalized)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg (vhValueFull)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic (IntGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG (shellIntegrandG shellIntegrandG_fibre)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBound (norm_Fh_le norm_vhValue_le)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary (Fh)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBoundG

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- Uniform bound on the full value: `‖vhValueFull k h g∞ X‖ ≤ C` for every finite `X`, when
`det g∞ > 0`. -/
theorem norm_vhValueFull_le (k : ℤ) (h : CuspForm levelOne k) (C : ℝ)
    (hC : ∀ g : GL (Fin 2) ℝ, 0 < (Matrix.GeneralLinearGroup.det g).val → ‖Fh k ⇑h g‖ ≤ C)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (X : BinaryFiniteGL) :
    ‖vhValueFull k h gInf X‖ ≤ C := by
  unfold vhValueFull
  rw [ite_eq_left hg]
  exact norm_vhValue_le k h C hC gInf hg X

/-- Pointwise bound of the literal integrand at `g_f` on the shell `pairShell p s`:
`‖·‖ ≤ p^{-s k/2} · (‖normPower(det g_f) b‖ · C)`. -/
theorem norm_shellIntegrandG_le (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n) (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val)
    {C : ℝ}
    (hC : ∀ g : GL (Fin 2) ℝ, 0 < (Matrix.GeneralLinearGroup.det g).val →
      ‖Fh (-2 * I.halfWeight) ⇑h g‖ ≤ C)
    {s : ℕ} {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hz : z ∈ Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s) :
    ‖shellIntegrandG v I gf gInf z‖ ≤
      ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) *
        (‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2)‖ * C) := by
  obtain ⟨t, ht, hzt⟩ := ShellLitSet.exists_shellFibre hz
  have hzt' : Padic.pairLat (Rat.HeightOneSpectrum.primesEquiv v).val z =
      Padic.hermLat (Rat.HeightOneSpectrum.primesEquiv v).val t :=
    (Submodule.toAddSubgroup_inj _ _).1 hzt.2
  rw [shellIntegrandG_fibre v I h hform gInf hg gf gp hgp hgI ht hz hzt'
    (ShellLitFibre.shellB v t)
    (fun i j => ShellLitFibre.shellB_entry v (ShellLitSet.mem_hnfData_of_cyclic ht) i j),
    norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (norm_vhValueFull_le _ h C hC gInf hg (ιGL v (ShellLitFibre.shellB v t) * (gf * ιGL v gp⁻¹)))
    (norm_nonneg _))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- On each shell `pairShell p s` (`s ≥ 1`) the literal integrand at `g_f` is integrable
(finite union of cyclic fibres on which it is constant). -/
theorem shell_integrableOn_G (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n) (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val)
    {s : ℕ} (hs : 1 ≤ s) :
    IntegrableOn (shellIntegrandG v I gf gInf)
      (Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s)
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) := by
  have key := ShellFibreSum.fibre_sum_integral
    ((finitePadicMeasure v).prod (finitePadicMeasure v))
    (T := cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val s)
    (F := fun t => ShellLitSet.shellFibre (Rat.HeightOneSpectrum.primesEquiv v).val s t)
    (c := fun t => ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        vhValueFull (-2 * I.halfWeight) h gInf
          (ιGL v (ShellLitFibre.shellB v t) * (gf * ιGL v gp⁻¹)))
    (f := shellIntegrandG v I gf gInf)
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
      exact shellIntegrandG_fibre v I h hform gInf hg gf gp hgp hgI ht hz.1 hzt
        (ShellLitFibre.shellB v t)
        (fun i j => ShellLitFibre.shellB_entry v (ShellLitSet.mem_hnfData_of_cyclic ht) i j))
  exact key.1

/-- The shell integral of the norm is at most `p^{-s k/2} · D · p^{2s}`, for any integrand `f`
bounded pointwise on the shell by `p^{-s k/2} · D`, with `μ(shell) ≤ p^{2s}`. -/
theorem shell_integral_norm_le_const (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (w : ℤ) (f : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] → ℂ)
    {D : ℝ} (hD0 : 0 ≤ D) {s : ℕ} (hs : 1 ≤ s)
    (hint : IntegrableOn f (Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s)
      ((finitePadicMeasure v).prod (finitePadicMeasure v)))
    (hle : ∀ z ∈ Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s,
      ‖f z‖ ≤ ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
        (-(s : ℝ) * (((-2 * w : ℤ) : ℝ) / 2)) * D) :
    ∫ z in Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s,
        ‖f z‖ ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) ≤
      ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * w : ℤ) : ℝ) / 2)) * D *
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
      (-(s : ℝ) * (((-2 * w : ℤ) : ℝ) / 2)) * D :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hD0
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
          (-(s : ℝ) * (((-2 * w : ℤ) : ℝ) / 2)) * D) ∂((finitePadicMeasure v).prod
            (finitePadicMeasure v)) :=
        setIntegral_mono_on hint.norm (integrableOn_const hfin) hS hle
    _ = (1 - (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ 2)⁻¹) *
          ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * s) *
          (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
            (-(s : ℝ) * (((-2 * w : ℤ) : ℝ) / 2)) * D) := by
        rw [setIntegral_const, Measure.real, hmeas, ENNReal.toReal_ofReal hnonneg, smul_eq_mul]
    _ ≤ ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * s) *
          (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
            (-(s : ℝ) * (((-2 * w : ℤ) : ℝ) / 2)) * D) := by
        nlinarith [mul_nonneg (mul_nonneg hx hP) hc0]
    _ = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * w : ℤ) : ℝ) / 2)) * D *
        ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * s) := by ring

/-- **The shell sum at a general base point is summable for `k > 6`.** The constant is
`‖normPower(det g_f) b‖ · C` with `C` the uniform cusp-form bound. -/
theorem summable_shell_norm_G (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n) (h : CuspForm levelOne (-2 * I.halfWeight))
    (hk : 6 < -2 * I.halfWeight)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val) :
    Summable (fun r : ℕ => ∫ z in Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1),
      ‖shellIntegrandG v I gf gInf z‖
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
    (fun r => ?_) ((summable_geometric_of_lt_one hq0 hq1).mul_left
      (‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
        (((-2 * I.halfWeight : ℤ) : ℂ) / 2)‖ * C * q))
  have hb := shell_integral_norm_le_const v I.halfWeight
    (shellIntegrandG v I gf gInf)
    (D := ‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
        (((-2 * I.halfWeight : ℤ) : ℂ) / 2)‖ * C)
    (mul_nonneg (norm_nonneg _) hC0) (s := r + 1) (by omega)
    (shell_integrableOn_G v I h hform gInf hg gf gp hgp hgI (by omega : 1 ≤ r + 1))
    (fun z hz => norm_shellIntegrandG_le v I h hform gInf hg gf gp hgp hgI hC hz)
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
  calc _ = (‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
        (((-2 * I.halfWeight : ℤ) : ℂ) / 2)‖ * C) *
        (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(((r + 1 : ℕ) : ℝ)) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) *
        ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (2 * (r + 1))) := by ring
    _ = (‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
        (((-2 * I.halfWeight : ℤ) : ℂ) / 2)‖ * C) * q ^ (r + 1) := by rw [key]
    _ = (‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
        (((-2 * I.halfWeight : ℤ) : ℂ) / 2)‖ * C * q) * q ^ r := by ring

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBoundG

end
