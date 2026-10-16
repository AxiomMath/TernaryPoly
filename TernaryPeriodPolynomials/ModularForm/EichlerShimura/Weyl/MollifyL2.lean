module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.Mollify
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section


/-!
# `L²` estimates for the mollifiers on `ℂ`

`‖mol n f‖₂ ≤ ‖f‖₂` and `mol n f → f` in `L²` for every `f ∈ L²(ℂ; X)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff Convolution ENNReal

theorem sq_integral_le_of_prob {w a : ℂ → ℝ} (hw : ∀ t, 0 ≤ w t) (hw1 : ∫ t, w t = 1)
    (hwi : Integrable w) (hwa : Integrable fun t => w t * a t)
    (hwa2 : Integrable fun t => w t * a t ^ 2) :
    (∫ t, w t * a t) ^ 2 ≤ ∫ t, w t * a t ^ 2 := by
  set m := ∫ t, w t * a t with hm
  have h0 : 0 ≤ ∫ t, w t * (a t - m) ^ 2 :=
    integral_nonneg fun t => mul_nonneg (hw t) (sq_nonneg _)
  have e : ∀ t, w t * (a t - m) ^ 2 = w t * a t ^ 2 - 2 * m * (w t * a t) + m ^ 2 * w t :=
    fun t => by ring
  have i1 : Integrable fun t => 2 * m * (w t * a t) := hwa.const_mul _
  have i2 : Integrable fun t => m ^ 2 * w t := hwi.const_mul _
  simp only [e] at h0
  have h1 := integral_add (f := fun t => w t * a t ^ 2 - 2 * m * (w t * a t))
    (g := fun t => m ^ 2 * w t) (hwa2.sub i1) i2
  have h2 := integral_sub (f := fun t => w t * a t ^ 2) (g := fun t => 2 * m * (w t * a t)) hwa2 i1
  rw [integral_const_mul] at h2
  have h3 : ∫ t, m ^ 2 * w t = m ^ 2 := by rw [integral_const_mul, hw1, mul_one]
  have h4 : ∫ t, w t * a t = m := rfl
  rw [h1, h2, h3, h4] at h0
  nlinarith

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem mol_sq_bound (n : ℕ) {f : ℂ → X} (hf : MemLp f 2 volume) :
    Integrable (fun x => ‖mol n f x‖ ^ 2) ∧ ∫ x, ‖mol n f x‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 := by
  have hb : Integrable fun x => ‖f x‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hker : Continuous (ker n) := (ker_contDiff n).continuous
  have hcx : ∀ x, Integrable fun t => ker n t * ‖f (x - t)‖ := fun x =>
    (ker_compact n).convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hker (hf.norm.locallyIntegrable (by norm_num)) x
  have hcx2 : ∀ x, Integrable fun t => ker n t * ‖f (x - t)‖ ^ 2 := fun x =>
    (ker_compact n).convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hker hb.locallyIntegrable x
  set G : ℂ → ℝ := fun x => ∫ t, ker n t * ‖f (x - t)‖ ^ 2 with hG
  have hGconv : G = (ker n) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x => ‖f x‖ ^ 2 := by
    funext x
    simp [hG, convolution_def]
  have hGi : Integrable G := by
    rw [hGconv]
    exact (ker_integrable n).integrable_convolution _ hb
  have hGint : ∫ x, G x = ∫ x, ‖f x‖ ^ 2 := by
    rw [hGconv, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) (ker_integrable n) hb]
    simp [integral_ker]
  have hpt : ∀ x, ‖mol n f x‖ ^ 2 ≤ G x := by
    intro x
    have h1 : ‖mol n f x‖ ≤ ∫ t, ker n t * ‖f (x - t)‖ := by
      rw [mol_apply]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
        (Eventually.of_forall fun t => ?_)))
      simp [norm_smul, abs_of_nonneg (ker_nonneg n t)]
    have h2 := sq_integral_le_of_prob (w := ker n) (a := fun t => ‖f (x - t)‖)
      (ker_nonneg n) (integral_ker n) (ker_integrable n) (hcx x) (hcx2 x)
    calc ‖mol n f x‖ ^ 2 ≤ (∫ t, ker n t * ‖f (x - t)‖) ^ 2 := by
          gcongr
      _ ≤ G x := h2
  have hmeas : AEStronglyMeasurable (fun x => ‖mol n f x‖ ^ 2) volume :=
    ((mol_contDiff n hfl).continuous.norm.pow 2).aestronglyMeasurable
  have hint : Integrable (fun x => ‖mol n f x‖ ^ 2) :=
    hGi.mono' hmeas (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hpt x)
  exact ⟨hint, hGint ▸ integral_mono hint hGi hpt⟩

omit [NormedSpace ℝ X] in
theorem eLpNorm_two_eq {f : ℂ → X} (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume = ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖ ^ 2)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [Real.sqrt_eq_rpow, one_div]

theorem eLpNorm_mol_le (n : ℕ) {f : ℂ → X} (hf : MemLp f 2 volume) :
    eLpNorm (mol n f) 2 volume ≤ eLpNorm f 2 volume := by
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  obtain ⟨hi, hle⟩ := mol_sq_bound n hf
  have hm : MemLp (mol n f) 2 volume :=
    (memLp_two_iff_integrable_sq_norm (mol_contDiff n hfl).continuous.aestronglyMeasurable).mpr hi
  rw [eLpNorm_two_eq hm, eLpNorm_two_eq hf]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hle)

theorem mol_sub (n : ℕ) {f h : ℂ → X} (hf : LocallyIntegrable f volume)
    (hh : LocallyIntegrable h volume) (x : ℂ) :
    mol n (fun z => f z - h z) x = mol n f x - mol n h x := by
  have a1 := (ker_compact n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (ker_contDiff n).continuous hf x
  have a2 := (ker_compact n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (ker_contDiff n).continuous hh x
  simp only [mol_apply, smul_sub]
  exact integral_sub a1 a2

theorem norm_mol_le_of_bound (n : ℕ) {f : ℂ → X} {M : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (x : ℂ) : ‖mol n f x‖ ≤ M := by
  rw [mol_apply]
  calc ‖∫ t, ker n t • f (x - t)‖ ≤ ∫ t, ker n t * M :=
        norm_integral_le_of_norm_le ((ker_integrable n).mul_const M) (Eventually.of_forall fun t => by
          rw [norm_smul, Real.norm_of_nonneg (ker_nonneg n t)]
          exact mul_le_mul_of_nonneg_left (hM _) (ker_nonneg n t))
    _ = M := by rw [integral_mul_const, integral_ker, one_mul]

theorem tendsto_mol_continuous [CompleteSpace X] {h : ℂ → X} (hc : Continuous h) (hs : HasCompactSupport h) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => mol n h x - h x) 2 volume) atTop (𝓝 0) := by
  have hl : LocallyIntegrable h volume := hc.locallyIntegrable
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set K₁ : Set ℂ := cthickening 1 (tsupport h) with hK₁
  have hK₁c : IsCompact K₁ := hs.isCompact.cthickening
  have hzero : ∀ n : ℕ, ∀ x, x ∉ K₁ → mol n h x - h x = 0 := by
    intro n x hx
    have h1 : x ∉ cthickening (1 / ((n : ℝ) + 1)) (tsupport h) := fun hx' =>
      hx (cthickening_mono (by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) _ hx')
    have h2 : h x = 0 := image_eq_zero_of_notMem_tsupport fun hx' =>
      hx (self_subset_cthickening _ hx')
    rw [mol_eq_zero n (K := tsupport h) (Eventually.of_forall fun z hz =>
      image_eq_zero_of_notMem_tsupport hz) h1, h2, sub_zero]
  have hcont : ∀ n : ℕ, Continuous fun x => mol n h x - h x := fun n =>
    (mol_contDiff n hl).continuous.sub hc
  have hF0 : Tendsto (fun n : ℕ => ∫ x, ‖mol n h x - h x‖ ^ 2) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := volume)
      (F := fun (n : ℕ) (x : ℂ) => ‖mol n h x - h x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (bound := K₁.indicator fun _ => (2 * M) ^ 2)
      (fun n => ((hcont n).norm.pow 2).aestronglyMeasurable)
      ((integrable_indicator_iff hK₁c.measurableSet).mpr (integrableOn_const hK₁c.measure_lt_top.ne)) ?_ ?_
    · simpa using this
    · intro n
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ K₁
      · rw [indicator_of_mem hx, Real.norm_of_nonneg (by positivity)]
        have h1 : ‖mol n h x - h x‖ ≤ 2 * M :=
          (norm_sub_le _ _).trans (by linarith [norm_mol_le_of_bound n hM x, hM x])
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      · rw [indicator_of_notMem hx, hzero n x hx]
        simp
    · refine Eventually.of_forall fun x => ?_
      have h1 : Tendsto (fun n : ℕ => mol n h x) atTop (𝓝 (h x)) :=
        ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) (φ := bump)
          (l := atTop) (g := h) (by
            simp only [bump]
            exact tendsto_one_div_add_atTop_nhds_zero_nat) hc x
      have h2 : Tendsto (fun n : ℕ => ‖mol n h x - h x‖ ^ 2) atTop (𝓝 (‖h x - h x‖ ^ 2)) :=
        ((h1.sub_const (h x)).norm).pow 2 |>.congr' (Eventually.of_forall fun _ => rfl)
      simpa using h2
  have hmem : ∀ n : ℕ, MemLp (fun x => mol n h x - h x) 2 volume := fun n =>
    (hcont n).memLp_of_hasCompactSupport (HasCompactSupport.intro hK₁c (hzero n))
  have : (fun n : ℕ => eLpNorm (fun x => mol n h x - h x) 2 volume) =
      fun n : ℕ => ENNReal.ofReal (Real.sqrt (∫ x, ‖mol n h x - h x‖ ^ 2)) :=
    funext fun n => eLpNorm_two_eq (hmem n)
  rw [this]
  have h3 := (Real.continuous_sqrt.tendsto 0).comp hF0
  have h4 := ENNReal.tendsto_ofReal h3
  simpa using h4

theorem tendsto_mol [CompleteSpace X] {f : ℂ → X} (hf : MemLp f 2 volume) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => mol n f x - f x) 2 volume) atTop (𝓝 0) := by
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := by
    intro h0
    rw [ENNReal.div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact hε.ne' h0
    · simp at h0
  obtain ⟨h, hhs, hfh, hhc, hhm⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hε3
  have hhl : LocallyIntegrable h volume := hhc.locallyIntegrable
  have hlim := (ENNReal.tendsto_nhds_zero.mp (tendsto_mol_continuous hhc hhs)) (ε / 3)
    (ENNReal.div_pos hε.ne' (by simp))
  filter_upwards [hlim] with n hn
  have hfh' : MemLp (fun x => f x - h x) 2 volume := hf.sub hhm
  have e : (fun x => mol n f x - f x) = fun x => mol n (fun z => f z - h z) x +
      (mol n h x - h x) + (h x - f x) := by
    funext x
    rw [mol_sub n hfl hhl x]
    abel
  have m1 : AEStronglyMeasurable (fun x => mol n (fun z => f z - h z) x) volume :=
    (mol_contDiff n (hfh'.locallyIntegrable (by norm_num))).continuous.aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun x => mol n h x - h x) volume :=
    ((mol_contDiff n hhl).continuous.sub hhc).aestronglyMeasurable
  have m3 : AEStronglyMeasurable (fun x => h x - f x) volume :=
    hhc.aestronglyMeasurable.sub hf.aestronglyMeasurable
  have b1 : eLpNorm (fun x => mol n (fun z => f z - h z) x) 2 volume ≤ ε / 3 :=
    (eLpNorm_mol_le n hfh').trans hfh
  have b3 : eLpNorm (fun x => h x - f x) 2 volume ≤ ε / 3 := by
    have : eLpNorm (fun x => h x - f x) 2 volume = eLpNorm (f - h) 2 volume :=
      eLpNorm_sub_comm h f 2 volume
    rw [this]
    exact hfh
  rw [e]
  calc eLpNorm (fun x => mol n (fun z => f z - h z) x + (mol n h x - h x) + (h x - f x)) 2 volume
      ≤ eLpNorm (fun x => mol n (fun z => f z - h z) x + (mol n h x - h x)) 2 volume +
          eLpNorm (fun x => h x - f x) 2 volume :=
        eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (fun x => mol n (fun z => f z - h z) x) 2 volume +
          eLpNorm (fun x => mol n h x - h x) 2 volume) +
          eLpNorm (fun x => h x - f x) 2 volume := by
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := ENNReal.add_thirds ε

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
