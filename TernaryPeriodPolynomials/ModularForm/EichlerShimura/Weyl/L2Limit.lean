module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.Garding

@[expose] public section


/-!
# `L²` limits, the pairing estimate, and the Gårding estimate for mollified weak solutions

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace ENNReal

section Pairing

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
theorem L2s.neg {K : Set ℂ} {v : ℂ → X} (h : L2s K v) : L2s K fun z => - v z :=
  ⟨h.1.neg, by
    filter_upwards [h.2] with z hz hzK
    simp [hz hzK]⟩

omit [NormedSpace ℝ X] in
theorem L2s.sub {K : Set ℂ} {v w : ℂ → X} (h : L2s K v) (h' : L2s K w) :
    L2s K fun z => v z - w z :=
  ⟨h.1.sub h'.1, by
    filter_upwards [h.2, h'.2] with z h1 h2 hz
    simp [h1 hz, h2 hz]⟩

omit [NormedSpace ℝ X] in
theorem integral_norm_le_sqrt {K : Set ℂ} (hK : IsCompact K) {h : ℂ → X} (hh : L2s K h) :
    ∫ z, ‖h z‖ ≤ Real.sqrt (volume K).toReal * Real.sqrt (∫ z, ‖h z‖ ^ 2) := by
  have hfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have h1 : (fun z => ‖h z‖) =ᵐ[volume] fun z => K.indicator (fun _ => (1 : ℝ)) z * ‖h z‖ := by
    filter_upwards [hh.2] with z hz
    by_cases hzK : z ∈ K
    · simp [hzK]
    · simp [hzK, hz hzK]
  rw [integral_congr_ae h1]
  have hind : MemLp (K.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact memLp_indicator_const (μ := volume) 2 hK.measurableSet (1 : ℝ) (Or.inr hfin)
  have hnorm : MemLp (fun z => ‖h z‖) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact hh.1.norm
  have := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) (p := 2) (q := 2)
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z)
    (Eventually.of_forall fun z => norm_nonneg (h z)) hind hnorm
  refine this.trans (le_of_eq ?_)
  have e1 : ∫ z, (K.indicator (fun _ => (1 : ℝ)) z) ^ (2 : ℝ) = (volume K).toReal := by
    have : ∀ z, (K.indicator (fun _ => (1 : ℝ)) z) ^ (2 : ℝ) = K.indicator (fun _ => (1 : ℝ)) z := by
      intro z
      by_cases hz : z ∈ K <;> simp [hz]
    simp only [this]
    rw [integral_indicator_const _ hK.measurableSet]
    simp
    rfl
  have e2 : ∫ z, ‖h z‖ ^ (2 : ℝ) = ∫ z, ‖h z‖ ^ 2 := by
    simp only [Real.rpow_two]
  rw [e1, e2, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

theorem integrable_smul_bdd {φ : ℂ → ℝ} {C : ℝ} (hφ : Continuous φ) (hC : ∀ z, |φ z| ≤ C)
    {v : ℂ → X} (hv : Integrable v) : Integrable fun z => φ z • v z :=
  hv.smul_of_top_right (memLp_top_of_bound hφ.aestronglyMeasurable C
    (Eventually.of_forall fun z => by simpa using hC z))

theorem norm_integral_smul_le [CompleteSpace X] {K : Set ℂ} (hK : IsCompact K) {φ : ℂ → ℝ} {C : ℝ}
    (hC : ∀ z, |φ z| ≤ C) {h : ℂ → X} (hh : L2s K h) :
    ‖∫ z, φ z • h z‖ ≤ C * (Real.sqrt (volume K).toReal * Real.sqrt (∫ z, ‖h z‖ ^ 2)) := by
  have hi : Integrable fun z => ‖h z‖ := (hh.integrable hK).norm
  calc ‖∫ z, φ z • h z‖ ≤ ∫ z, C * ‖h z‖ :=
        norm_integral_le_of_norm_le (hi.const_mul C) (Eventually.of_forall fun z => by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _))
    _ = C * ∫ z, ‖h z‖ := integral_const_mul _ _
    _ ≤ _ := by
        have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
        exact mul_le_mul_of_nonneg_left (integral_norm_le_sqrt hK hh) hC0

theorem tendsto_integral_smul [CompleteSpace X] {K : Set ℂ} (hK : IsCompact K) {φ : ℂ → ℝ}
    {C : ℝ} (hφ : Continuous φ) (hC : ∀ z, |φ z| ≤ C) {a : ℕ → ℂ → X} {a' : ℂ → X}
    (ha : ∀ n, L2s K (a n)) (ha' : L2s K a')
    (hconv : Tendsto (fun n => eLpNorm (fun z => a n z - a' z) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, φ z • a n z) atTop (𝓝 (∫ z, φ z • a' z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun n => C * (Real.sqrt (volume K).toReal *
      (eLpNorm (fun z => a n z - a' z) 2 volume).toReal)) atTop (𝓝 (C * (Real.sqrt (volume K).toReal * 0))) :=
    (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv).const_mul _).const_mul _
  rw [mul_zero, mul_zero] at hb
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
  have hd := norm_integral_smul_le hK hC ((ha n).sub ha')
  have e1 : (∫ z, φ z • a n z) - ∫ z, φ z • a' z = ∫ z, φ z • (a n z - a' z) := by
    rw [← integral_sub (integrable_smul_bdd hφ hC ((ha n).integrable hK))
      (integrable_smul_bdd hφ hC (ha'.integrable hK))]
    simp only [smul_sub]
  have e2 : Real.sqrt (∫ z, ‖a n z - a' z‖ ^ 2) = (eLpNorm (fun z => a n z - a' z) 2 volume).toReal := by
    rw [eLpNorm_two_eq ((ha n).sub ha').1, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  rw [e1]
  calc ‖∫ z, φ z • (a n z - a' z)‖ ≤ _ := hd
    _ = _ := by rw [e2]

end Pairing

section Limit

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [NormedSpace ℝ X] in
/-- A sequence of `L²` functions supported in `K` which is Cauchy in `L²` has an `L²` limit
supported in `K`. -/
theorem exists_L2_limit {K : Set ℂ} (hK : IsCompact K) {a : ℕ → ℂ → X} (ha : ∀ n, L2s K (a n))
    (hc : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ m, N ≤ m →
      eLpNorm (fun z => a n z - a m z) 2 volume ≤ ε) :
    ∃ g : ℂ → X, L2s K g ∧
      Tendsto (fun n => eLpNorm (fun z => a n z - g z) 2 volume) atTop (𝓝 0) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let G : ℕ → Lp X 2 volume := fun n => (ha n).1.toLp (a n)
  have hdist : ∀ n m, dist (G n) (G m) = (eLpNorm (fun z => a n z - a m z) 2 volume).toReal := by
    intro n m
    rw [Lp.dist_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (G n) (G m), MemLp.coeFn_toLp (ha n).1,
      MemLp.coeFn_toLp (ha m).1] with z h1 h2 h3
    simp only [Pi.sub_apply] at h1 ⊢
    exact congrArg₂ (· - ·) h2 h3
  have hcs : CauchySeq G := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ENNReal.ofReal (ε / 2)) (by positivity)
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [hdist]
    have := hN n hn m hm
    have h2 : (eLpNorm (fun z => a n z - a m z) 2 volume).toReal ≤ ε / 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    linarith
  obtain ⟨Gl, hG⟩ := cauchySeq_tendsto_of_complete hcs
  have hlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' G Gl).mp hG
  have hae : ∀ n, (fun z => a n z - Gl z) =ᵐ[volume] ⇑(G n) - ⇑Gl := by
    intro n
    filter_upwards [MemLp.coeFn_toLp (ha n).1] with z hz
    simp only [Pi.sub_apply, G, hz]
  have hlim' : Tendsto (fun n => eLpNorm (fun z => a n z - Gl z) 2 volume) atTop (𝓝 0) := by
    refine hlim.congr fun n => (eLpNorm_congr_ae (hae n)).symm
  refine ⟨Gl, ⟨Lp.memLp Gl, ?_⟩, hlim'⟩
  -- support in `K`
  have h0 : eLpNorm (⇑Gl) 2 (volume.restrict Kᶜ) = 0 := by
    have hb : ∀ n, eLpNorm (⇑Gl) 2 (volume.restrict Kᶜ) ≤
        eLpNorm (fun z => a n z - Gl z) 2 volume := by
      intro n
      have hz : (⇑Gl) =ᵐ[volume.restrict Kᶜ] fun z => - (a n z - Gl z) := by
        rw [EventuallyEq, ae_restrict_iff' hK.measurableSet.compl]
        filter_upwards [(ha n).2] with z hz hzK
        simp [hz hzK]
      calc eLpNorm (⇑Gl) 2 (volume.restrict Kᶜ)
          = eLpNorm (fun z => -(a n z - Gl z)) 2 (volume.restrict Kᶜ) := eLpNorm_congr_ae hz
        _ = eLpNorm (fun z => a n z - Gl z) 2 (volume.restrict Kᶜ) := eLpNorm_neg _ _ _
        _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
    exact le_antisymm (ge_of_tendsto' hlim' hb) bot_le
  have := (eLpNorm_eq_zero_iff (by norm_num)).mp h0
  rw [EventuallyEq, ae_restrict_iff' hK.measurableSet.compl] at this
  filter_upwards [this] with z hz hzK
  simpa using hz hzK

end Limit

section OneStep

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  {P : Fin 2 → X →L[ℝ] X}

theorem sq_integral_deriv_le (hP : DiracPair P) {K : Set ℂ} (hK : IsCompact K) {v f : ℂ → X}
    (hv : L2s K v) (h : WeakEq P v f) (n m : ℕ) (j : Fin 2) :
    ∫ z, ‖fderiv ℝ (mol n v) z (dir j) - fderiv ℝ (mol m v) z (dir j)‖ ^ 2 ≤
      ∫ z, ‖mol n f z - mol m f z‖ ^ 2 := by
  have hvl : LocallyIntegrable v volume := (hv.integrable hK).locallyIntegrable
  have c1 := mol_contDiff n hvl
  have c2 := mol_contDiff m hvl
  have k1 := mol_hasCompactSupport n hK hv.2
  have k2 := mol_hasCompactSupport m hK hv.2
  have hwc : ContDiff ℝ ∞ fun z => mol n v z - mol m v z := c1.sub c2
  have hwk : HasCompactSupport fun z => mol n v z - mol m v z := k1.sub k2
  have hd : ∀ z e, fderiv ℝ (fun z => mol n v z - mol m v z) z e =
      fderiv ℝ (mol n v) z e - fderiv ℝ (mol m v) z e := fun z e => by
    rw [fderiv_fun_sub (c1.differentiable (by simp) z) (c2.differentiable (by simp) z)]
    rfl
  have hsum : ∀ z, ∑ i, P i (fderiv ℝ (fun z => mol n v z - mol m v z) z (dir i)) =
      mol n f z - mol m f z := fun z => by
    simp only [hd, map_sub, Finset.sum_sub_distrib]
    rw [mol_weakEq n h hvl z, mol_weakEq m h hvl z]
  have g := garding hP hwc hwk
  simp only [hsum] at g
  simp only [hd] at g
  have i0 := integrable_norm_sq_fderiv hwc hwk (dir 0)
  have i1 := integrable_norm_sq_fderiv hwc hwk (dir 1)
  simp only [hd] at i0 i1
  rw [← g]
  refine integral_mono (by fin_cases j <;> assumption) (i0.add i1) fun z => ?_
  fin_cases j
  · exact le_add_of_nonneg_right (sq_nonneg _)
  · exact le_add_of_nonneg_left (sq_nonneg _)

end OneStep

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
