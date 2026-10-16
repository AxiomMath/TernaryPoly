module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.PartitionOfUnity

@[expose] public section


/-!
# Invariant height cutoffs on the upper half plane

`height z = sup_g Im(g z)` is the height of the reduced point of the `SL(2, ℤ)`-orbit of `z`
(attained, `exists_height_eq`; invariant, `height_mob`). Above height one it is locally the
imaginary part of a single translate (`height_eq_of_one_lt`), because a point of height `> 1`
is not moved higher by any element of `SL(2, ℤ)` (`im_smul_le_of_one_lt_im`).

For `T > 1` the cutoff `heightCutoff T = ψ(log height / log T)`, with a smooth step `ψ`, is smooth
on `U` (`contDiffOn_heightCutoff`), `SL(2, ℤ)`-invariant (`heightCutoff_mob`), takes values in
`[0, 1]`, equals `1` where `height ≤ T` and `0` where `height ≥ T²`, is monotone in `T`, and its
support is compact modulo `SL(2, ℤ)` (`exists_compact_of_heightCutoff_ne_zero`). Its gradient is
`O(1 / (Im z · log T))` uniformly (`norm_fderiv_heightCutoff_le`, `norm_im_mul_dbar_le`). These
are the truncations of the global integration by parts in the Hodge step of the Eichler–Shimura
route.

Written by Claude Opus 5.5.
-/

open UpperHalfPlane ModularGroup Complex Filter Topology
open scoped Modular MatrixGroups ContDiff
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.Height

open TernaryPeriodPolynomials.Argument.ESFoundations.Partition

/-! ### The height -/

/-- The height of `z`: the largest imaginary part in its `SL(2, ℤ)`-orbit. -/
def height (z : ℂ) : ℝ := ⨆ g : SL(2, ℤ), (mob g z).im

theorem exists_height_eq (z : ℂ) :
    ∃ g₀ : SL(2, ℤ), height z = (mob g₀ z).im ∧ ∀ g : SL(2, ℤ), (mob g z).im ≤ height z := by
  obtain ⟨g₀, hg₀⟩ := ModularGroup.exists_max_im (UpperHalfPlane.ofComplex z)
  have hbdd : BddAbove (Set.range fun g : SL(2, ℤ) => (mob g z).im) :=
    ⟨(mob g₀ z).im, by rintro _ ⟨g, rfl⟩; exact hg₀ g⟩
  have heq : height z = (mob g₀ z).im :=
    le_antisymm (ciSup_le fun g => hg₀ g) (le_ciSup hbdd g₀)
  exact ⟨g₀, heq, fun g => heq ▸ hg₀ g⟩

theorem im_mob_le_height (g : SL(2, ℤ)) (z : ℂ) : (mob g z).im ≤ height z :=
  (exists_height_eq z).choose_spec.2 g

theorem height_pos (z : ℂ) : 0 < height z :=
  lt_of_lt_of_le (mob_mem 1 z) (im_mob_le_height 1 z)

theorem height_mob (h : SL(2, ℤ)) (z : ℂ) : height (mob h z) = height z := by
  obtain ⟨g₀, hg₀, hle⟩ := exists_height_eq (mob h z)
  obtain ⟨g₁, hg₁, hle'⟩ := exists_height_eq z
  apply le_antisymm
  · rw [hg₀, ← mob_mul]; exact im_mob_le_height _ _
  · rw [hg₁, show g₁ = g₁ * h⁻¹ * h by group, mob_mul]; exact im_mob_le_height _ _

/-- A point of height `> 1` is not moved higher. -/
theorem im_smul_le_of_one_lt_im (h : SL(2, ℤ)) {w : ℍ} (hw : 1 < w.im) : (h • w).im ≤ w.im := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have hN : 0 < Complex.normSq (denom h w) := Complex.normSq_pos.mpr (denom_ne_zero h w)
  rw [div_le_iff₀ hN]
  rw [Complex.normSq_apply, ModularGroup.denom_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.add_im, Complex.mul_im, zero_mul, sub_zero, add_zero, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  by_cases hc : h 1 0 = 0
  · have hdet := h.2
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    have hd : ((h 1 1 : ℤ) : ℝ) ^ 2 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨-, h11⟩ | ⟨-, h11⟩ <;>
        rw [h11] <;> norm_num
    rw [hc]
    simp only [Int.cast_zero, zero_mul, zero_add, mul_zero, add_zero]
    nlinarith [hd]
  · have hc1 : (1 : ℝ) ≤ ((h 1 0 : ℤ) : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ h 1 0 ^ 2 := by
        have := Int.one_le_abs hc
        nlinarith [sq_abs (h 1 0)]
      exact_mod_cast this
    have hy : 0 < w.im := w.im_pos
    nlinarith [sq_nonneg (((h 1 0 : ℤ) : ℝ) * w.re + ((h 1 1 : ℤ) : ℝ)),
      mul_le_mul_of_nonneg_right hc1 (sq_nonneg w.im)]

/-- Above height one the height is the imaginary part of any translate exceeding one. -/
theorem height_eq_of_one_lt {g : SL(2, ℤ)} {z : ℂ} (hg : 1 < (mob g z).im) :
    height z = (mob g z).im := by
  apply le_antisymm _ (im_mob_le_height g z)
  obtain ⟨g₀, hg₀, -⟩ := exists_height_eq z
  rw [hg₀, show g₀ = g₀ * g⁻¹ * g by group, mob_mul, mob]
  have hw : mob g z = (((g • UpperHalfPlane.ofComplex z : ℍ)) : ℂ) := rfl
  rw [hw, UpperHalfPlane.ofComplex_apply]
  exact im_smul_le_of_one_lt_im _ hg

/-- A uniform local upper comparison of the imaginary parts of all translates. -/
theorem im_mob_le_of_near (g : SL(2, ℤ)) {z z₀ : ℂ} (hz₀ : 0 < z₀.im) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) (hz : ‖z - z₀‖ ≤ ε * z₀.im) :
    (mob g z).im * (1 - ε) ^ 2 ≤ (1 + ε) * (mob g z₀).im := by
  have him := Complex.abs_im_le_norm (z - z₀)
  rw [Complex.sub_im] at him
  have hzpos : 0 < z.im := by
    have := (abs_le.mp him).1
    nlinarith
  have hzU : z ∈ U := hzpos
  have hz₀U : z₀ ∈ U := hz₀
  set c : ℂ := ((g 1 0 : ℤ) : ℂ)
  set d : ℂ := ((g 1 1 : ℤ) : ℂ)
  have hform : ∀ {w : ℂ}, 0 < w.im → (mob g w).im = w.im / ‖c * w + d‖ ^ 2 := by
    intro w hw
    have h1 : mob g w = (((g • (⟨w, hw⟩ : ℍ) : ℍ)) : ℂ) := by
      rw [mob, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    rw [h1, UpperHalfPlane.coe_im, ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply,
      Complex.normSq_eq_norm_sq]
    rfl
  have hne₀ : c * z₀ + d ≠ 0 := denom_ne_zero' g hz₀U
  have hne : c * z + d ≠ 0 := denom_ne_zero' g hzU
  have hc_le : ‖c‖ * z₀.im ≤ ‖c * z₀ + d‖ := by
    have h := Complex.abs_im_le_norm (c * z₀ + d)
    have hc_im : (c * z₀ + d).im = ((g 1 0 : ℤ) : ℝ) * z₀.im := by
      simp [c, d, Complex.mul_im]
    rw [hc_im, abs_mul, abs_of_pos hz₀] at h
    have hcn : ‖c‖ = |((g 1 0 : ℤ) : ℝ)| := by simp [c, Complex.norm_intCast]
    rw [hcn]; exact h
  have hlow : (1 - ε) * ‖c * z₀ + d‖ ≤ ‖c * z + d‖ := by
    have h1 : ‖c * z₀ + d‖ ≤ ‖c * z + d‖ + ‖c‖ * ‖z - z₀‖ := by
      have : c * z₀ + d = (c * z + d) - c * (z - z₀) := by ring
      rw [this]
      exact le_trans (norm_sub_le _ _) (by rw [norm_mul])
    have h2 : ‖c‖ * ‖z - z₀‖ ≤ ε * ‖c * z₀ + d‖ := by
      calc ‖c‖ * ‖z - z₀‖ ≤ ‖c‖ * (ε * z₀.im) :=
            mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        _ = ε * (‖c‖ * z₀.im) := by ring
        _ ≤ ε * ‖c * z₀ + d‖ := mul_le_mul_of_nonneg_left hc_le hε0
    nlinarith
  have hN₀ : 0 < ‖c * z₀ + d‖ := norm_pos_iff.mpr hne₀
  have hN : 0 < ‖c * z + d‖ := norm_pos_iff.mpr hne
  have hsq : (1 - ε) ^ 2 * ‖c * z₀ + d‖ ^ 2 ≤ ‖c * z + d‖ ^ 2 := by
    have h0 : 0 ≤ (1 - ε) * ‖c * z₀ + d‖ := mul_nonneg (by linarith) hN₀.le
    have := mul_le_mul hlow hlow h0 hN.le
    nlinarith
  have hyz : z.im ≤ (1 + ε) * z₀.im := by
    have := (abs_le.mp him).2
    have h' : ‖z - z₀‖ ≤ ε * z₀.im := hz
    nlinarith
  have key : z.im * (1 - ε) ^ 2 * ‖c * z₀ + d‖ ^ 2 ≤ (1 + ε) * z₀.im * ‖c * z + d‖ ^ 2 :=
    calc z.im * (1 - ε) ^ 2 * ‖c * z₀ + d‖ ^ 2 = z.im * ((1 - ε) ^ 2 * ‖c * z₀ + d‖ ^ 2) := by ring
      _ ≤ z.im * ‖c * z + d‖ ^ 2 := mul_le_mul_of_nonneg_left hsq hzpos.le
      _ ≤ (1 + ε) * z₀.im * ‖c * z + d‖ ^ 2 := mul_le_mul_of_nonneg_right hyz (sq_nonneg _)
  rw [hform hzpos, hform hz₀, div_mul_eq_mul_div, mul_div_assoc',
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact key

theorem height_le_of_near {z z₀ : ℂ} (hz₀ : 0 < z₀.im) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hz : ‖z - z₀‖ ≤ ε * z₀.im) : height z * (1 - ε) ^ 2 ≤ (1 + ε) * height z₀ := by
  obtain ⟨g₀, hg₀, -⟩ := exists_height_eq z
  rw [hg₀]
  exact le_trans (im_mob_le_of_near g₀ hz₀ hε0 hε1 hz)
    (mul_le_mul_of_nonneg_left (im_mob_le_height g₀ z₀) (by linarith))

/-! ### The step and the cutoff -/

/-- The smooth step: `1` on `(-∞, 1]` and `0` on `[2, ∞)`. -/
def step (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem contDiff_step : ContDiff ℝ ∞ step :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem step_nonneg (t : ℝ) : 0 ≤ step t := Real.smoothTransition.nonneg _

theorem step_le_one (t : ℝ) : step t ≤ 1 := Real.smoothTransition.le_one _

theorem step_eq_one {t : ℝ} (ht : t ≤ 1) : step t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem step_eq_zero {t : ℝ} (ht : 2 ≤ t) : step t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem step_antitone : Antitone step := fun _ _ h =>
  Real.smoothTransition.monotone (by linarith)

theorem lt_two_of_step_ne_zero {t : ℝ} (h : step t ≠ 0) : t < 2 := by
  by_contra h'
  exact h (step_eq_zero (not_lt.mp h'))

/-- The invariant height cutoff `ψ(log height / log T)`. -/
def heightCutoff (T : ℝ) (z : ℂ) : ℝ := step (Real.log (height z) / Real.log T)

theorem heightCutoff_nonneg (T : ℝ) (z : ℂ) : 0 ≤ heightCutoff T z := step_nonneg _

theorem heightCutoff_le_one (T : ℝ) (z : ℂ) : heightCutoff T z ≤ 1 := step_le_one _

/-- The cutoff is `SL(2, ℤ)`-invariant. -/
theorem heightCutoff_mob (T : ℝ) (g : SL(2, ℤ)) (z : ℂ) :
    heightCutoff T (mob g z) = heightCutoff T z := by
  rw [heightCutoff, heightCutoff, height_mob]

theorem heightCutoff_eq_one {T : ℝ} (hT : 1 < T) {z : ℂ} (h : height z ≤ T) :
    heightCutoff T z = 1 := by
  apply step_eq_one
  have hlog : 0 < Real.log T := Real.log_pos hT
  rw [div_le_one hlog]
  exact Real.log_le_log (height_pos z) h

theorem heightCutoff_eq_zero {T : ℝ} (hT : 1 < T) {z : ℂ} (h : T ^ 2 ≤ height z) :
    heightCutoff T z = 0 := by
  apply step_eq_zero
  have hlog : 0 < Real.log T := Real.log_pos hT
  rw [le_div_iff₀ hlog]
  have := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at this
  push_cast at this
  linarith

theorem height_lt_of_heightCutoff_ne_zero {T : ℝ} (hT : 1 < T) {z : ℂ}
    (h : heightCutoff T z ≠ 0) : height z < T ^ 2 := by
  by_contra h'
  exact h (heightCutoff_eq_zero hT (not_lt.mp h'))

/-- The cutoff increases with `T`. -/
theorem heightCutoff_mono {T T' : ℝ} (hT : 1 < T) (hTT : T ≤ T') (z : ℂ) :
    heightCutoff T z ≤ heightCutoff T' z := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hlog' : Real.log T ≤ Real.log T' := Real.log_le_log (by linarith) hTT
  rcases le_or_gt (Real.log (height z)) 0 with h | h
  · rw [heightCutoff, heightCutoff, step_eq_one, step_eq_one]
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg h (by linarith)) zero_le_one
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg h hlog.le) zero_le_one
  · exact step_antitone (div_le_div_of_nonneg_left h.le hlog hlog')

/-- The cutoff is smooth on the upper half plane. -/
theorem contDiffOn_heightCutoff {T : ℝ} (hT : 1 < T) : ContDiffOn ℝ ∞ (heightCutoff T) U := by
  refine contDiffOn_of_locally_contDiffOn fun z₀ hz₀ => ?_
  by_cases h1 : 1 < height z₀
  · obtain ⟨g₀, hg₀, -⟩ := exists_height_eq z₀
    have hcont : ContinuousOn (fun z => (mob g₀ z).im) U :=
      Complex.continuous_im.comp_continuousOn (contDiffOn_mob g₀ (n := 0)).continuousOn
    refine ⟨U ∩ (fun z => (mob g₀ z).im) ⁻¹' Set.Ioi 1,
      hcont.isOpen_inter_preimage isOpen_U isOpen_Ioi, ⟨hz₀, by
        show 1 < (mob g₀ z₀).im
        rw [← hg₀]; exact h1⟩, ?_⟩
    have hsmooth : ContDiffOn ℝ ∞
        (fun z => step (Real.log (mob g₀ z).im / Real.log T)) U := by
      refine contDiff_step.comp_contDiffOn (ContDiffOn.div_const ?_ _)
      exact ContDiffOn.log (Complex.imCLM.contDiff.comp_contDiffOn (contDiffOn_mob g₀))
        fun z _ => (mob_mem g₀ z).ne'
    refine (hsmooth.mono Set.inter_subset_left).congr ?_
    intro z hz
    rw [heightCutoff, height_eq_of_one_lt hz.2.2]
  · have hy : 0 < z₀.im := hz₀
    set ε : ℝ := (T - 1) / (18 * T) with hε
    have hT0 : 0 < T := by linarith
    have hε0 : 0 < ε := by positivity
    have hTε : T * ε = (T - 1) / 18 := by rw [hε]; field_simp
    have hε1 : ε ≤ 1 / 18 := by
      rw [hε, div_le_iff₀ (by positivity)]
      linarith
    refine ⟨Metric.ball z₀ (ε * z₀.im), Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
      ?_⟩
    refine (contDiffOn_const (c := (1 : ℝ))).congr fun z hz => ?_
    have hz' : ‖z - z₀‖ ≤ ε * z₀.im := by
      have := hz.2
      rw [Metric.mem_ball, dist_eq_norm] at this
      exact this.le
    have hcomp := height_le_of_near hy hε0.le (by linarith) hz'
    have hle : height z ≤ T := by
      by_contra hlt
      push Not at hlt
      have h2 : height z₀ ≤ 1 := not_lt.mp h1
      have h3 : T * (1 - ε) ^ 2 < height z * (1 - ε) ^ 2 :=
        mul_lt_mul_of_pos_right hlt (by nlinarith)
      have h4 : (1 + ε) * height z₀ ≤ 1 + ε := by nlinarith
      nlinarith
    exact heightCutoff_eq_one hT hle

/-- The support of the cutoff is compact modulo `SL(2, ℤ)`. -/
theorem exists_compact_of_heightCutoff_ne_zero {T : ℝ} (hT : 1 < T) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ ∀ z ∈ U, heightCutoff T z ≠ 0 →
      ∃ g : SL(2, ℤ), ∃ w ∈ K, z = mob g w := by
  set K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I) ''
    (Set.Icc (-1 / 2) (1 / 2) ×ˢ Set.Icc (1 / 2) (T ^ 2)) with hK
  refine ⟨K, (isCompact_Icc.prod isCompact_Icc).image (by fun_prop), ?_, ?_⟩
  · rintro _ ⟨p, ⟨-, hp⟩, rfl⟩
    show 0 < ((p.1 : ℂ) + p.2 * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
    linarith [hp.1]
  · intro z hz hne
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd (⟨z, hz⟩ : ℍ)
    have hw : mob g z = (((g • (⟨z, hz⟩ : ℍ) : ℍ)) : ℂ) := by
      rw [mob, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have him4 := three_le_four_mul_im_sq_of_mem_fd hg
    have hre : |(g • (⟨z, hz⟩ : ℍ)).re| ≤ 1 / 2 := hg.2
    have hpos := (g • (⟨z, hz⟩ : ℍ)).im_pos
    have hup : (mob g z).im < T ^ 2 :=
      lt_of_le_of_lt (im_mob_le_height g z) (height_lt_of_heightCutoff_ne_zero hT hne)
    refine ⟨g⁻¹, mob g z, ⟨((mob g z).re, (mob g z).im), ⟨?_, ?_⟩, Complex.re_add_im _⟩, ?_⟩
    · show -1 / 2 ≤ (mob g z).re ∧ (mob g z).re ≤ 1 / 2
      rw [hw, UpperHalfPlane.coe_re]
      have := abs_le.mp hre
      constructor <;> linarith [this.1, this.2]
    · refine ⟨?_, hup.le⟩
      rw [hw]
      change 1 / 2 ≤ (g • (⟨z, hz⟩ : ℍ)).im
      nlinarith
    · rw [← mob_mul, inv_mul_cancel, mob_one hz]

/-! ### The gradient bound -/

theorem deriv_step_eq_zero {t : ℝ} (ht : t < 1 ∨ 2 < t) : deriv step t = 0 := by
  rcases ht with ht | ht
  · have h : step =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds ht] with u hu using step_eq_one (le_of_lt hu)
    rw [h.deriv_eq, deriv_const]
  · have h : step =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds ht] with u hu using step_eq_zero (le_of_lt hu)
    rw [h.deriv_eq, deriv_const]

theorem exists_bound_deriv_step : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv step t| ≤ C := by
  have hcont : Continuous (deriv step) :=
    (contDiff_step.continuous_deriv (by simp))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (1 : ℝ) 2
  · exact le_trans (by simpa [Real.norm_eq_abs] using hC t ht) (le_max_left _ _)
  · have : t < 1 ∨ 2 < t := by
      simp only [Set.mem_Icc, not_and_or, not_le] at ht
      exact ht
    rw [deriv_step_eq_zero this, abs_zero]
    exact le_max_right _ _

/-- Below height one the cutoff is locally constant. -/
theorem heightCutoff_eventually_one {T : ℝ} (hT : 1 < T) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (h1 : height z₀ ≤ 1) : ∀ᶠ z in 𝓝 z₀, heightCutoff T z = 1 := by
  have hy : 0 < z₀.im := hz₀
  set ε : ℝ := (T - 1) / (18 * T) with hε
  have hT0 : 0 < T := by linarith
  have hε0 : 0 < ε := by positivity
  have hTε : T * ε = (T - 1) / 18 := by rw [hε]; field_simp
  have hε1 : ε ≤ 1 / 18 := by
    rw [hε, div_le_iff₀ (by positivity)]
    linarith
  filter_upwards [Metric.ball_mem_nhds z₀ (by positivity : 0 < ε * z₀.im)] with z hz
  have hz' : ‖z - z₀‖ ≤ ε * z₀.im := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact hz.le
  have hcomp := height_le_of_near hy hε0.le (by linarith) hz'
  have hle : height z ≤ T := by
    by_contra hlt
    push Not at hlt
    have h3 : T * (1 - ε) ^ 2 < height z * (1 - ε) ^ 2 :=
      mul_lt_mul_of_pos_right hlt (by nlinarith)
    have h4 : (1 + ε) * height z₀ ≤ 1 + ε := by nlinarith
    nlinarith
  exact heightCutoff_eq_one hT hle

/-- Above height one the cutoff is locally `ψ((log T)⁻¹ log Im(g₀ z))`. -/
theorem heightCutoff_eventuallyEq {T : ℝ} {z₀ : ℂ} (hz₀ : z₀ ∈ U) {g₀ : SL(2, ℤ)}
    (hg₀ : 1 < (mob g₀ z₀).im) :
    heightCutoff T =ᶠ[𝓝 z₀]
      fun z => step ((Real.log T)⁻¹ * Real.log (mob g₀ z).im) := by
  have hcont : ContinuousOn (fun z => (mob g₀ z).im) U :=
    Complex.continuous_im.comp_continuousOn (contDiffOn_mob g₀ (n := 0)).continuousOn
  have hopen := hcont.isOpen_inter_preimage isOpen_U (isOpen_Ioi (a := (1 : ℝ)))
  filter_upwards [hopen.mem_nhds ⟨hz₀, hg₀⟩] with z hz
  rw [heightCutoff, height_eq_of_one_lt hz.2, div_eq_inv_mul]

/-- The derivative of a translate on `U`. -/
theorem hasDerivAt_mob (g : SL(2, ℤ)) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (mob g) (1 / (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) ^ 2) z := by
  set a : ℂ := ((g 0 0 : ℤ) : ℂ)
  set b : ℂ := ((g 0 1 : ℤ) : ℂ)
  set c : ℂ := ((g 1 0 : ℤ) : ℂ)
  set d : ℂ := ((g 1 1 : ℤ) : ℂ)
  have hne : c * z + d ≠ 0 := denom_ne_zero' g hz
  have hdet : a * d - b * c = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    simp only [a, b, c, d]
    exact_mod_cast this
  have hnum : HasDerivAt (fun w : ℂ => a * w + b) a z := by
    simpa using ((hasDerivAt_id z).const_mul a).add_const b
  have hden : HasDerivAt (fun w : ℂ => c * w + d) c z := by
    simpa using ((hasDerivAt_id z).const_mul c).add_const d
  have hq := hnum.div hden hne
  have hev : (fun w : ℂ => (a * w + b) / (c * w + d)) =ᶠ[𝓝 z] mob g := by
    filter_upwards [isOpen_U.mem_nhds hz] with w hw
    exact (mob_eq g hw).symm
  refine (hq.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  field_simp
  linear_combination hdet

theorem norm_denom_sq (g : SL(2, ℤ)) {z : ℂ} (hz : z ∈ U) :
    (mob g z).im = z.im / ‖((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)‖ ^ 2 := by
  have h1 : mob g z = (((g • (⟨z, hz⟩ : ℍ) : ℍ)) : ℂ) := by
    rw [mob, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  rw [h1, UpperHalfPlane.coe_im, ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply,
    Complex.normSq_eq_norm_sq]
  rfl

theorem norm_imCLM_comp_toSpanSingleton_le (u : ℂ) :
    ‖Complex.imCLM.comp ((ContinuousLinearMap.toSpanSingleton ℂ u).restrictScalars ℝ)‖ ≤ ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, Complex.imCLM_apply, Real.norm_eq_abs]
  refine le_trans (Complex.abs_im_le_norm _) ?_
  rw [smul_eq_mul, norm_mul, mul_comm]

/-- The gradient bound `‖dθ_T(z)‖ ≤ C / (log T · Im z)`, uniformly in `T`. -/
theorem exists_norm_fderiv_heightCutoff_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 < T → ∀ z ∈ U,
    ‖fderiv ℝ (heightCutoff T) z‖ ≤ C / (Real.log T * z.im) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_step
  refine ⟨C, hC0, fun T hT z hz => ?_⟩
  have hy : 0 < z.im := hz
  have hlog : 0 < Real.log T := Real.log_pos hT
  by_cases h1 : 1 < height z
  · obtain ⟨g₀, hg₀, -⟩ := exists_height_eq z
    have hgz : 1 < (mob g₀ z).im := hg₀ ▸ h1
    rw [(heightCutoff_eventuallyEq hz hgz).fderiv_eq]
    have hne : ((g₀ 1 0 : ℤ) : ℂ) * z + ((g₀ 1 1 : ℤ) : ℂ) ≠ 0 := denom_ne_zero' g₀ hz
    have hD := (hasDerivAt_mob g₀ hz).hasFDerivAt.restrictScalars ℝ
    have hIm := Complex.imCLM.hasFDerivAt.comp z hD
    have hwpos : 0 < (mob g₀ z).im := mob_mem g₀ z
    have hLog := hIm.log hwpos.ne'
    have hMul := hLog.const_mul (Real.log T)⁻¹
    have hStep := (contDiff_step.differentiable (by simp) _).hasDerivAt.comp_hasFDerivAt z hMul
    have hfd := hStep.fderiv
    simp only [Function.comp_def, Complex.imCLM_apply] at hfd
    rw [hfd, norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlog), abs_of_pos (inv_pos.mpr hwpos)]
    have hprod : ((mob g₀ z).im)⁻¹ *
        ‖(1 : ℂ) / (((g₀ 1 0 : ℤ) : ℂ) * z + ((g₀ 1 1 : ℤ) : ℂ)) ^ 2‖ = (z.im)⁻¹ := by
      have hn : ‖((g₀ 1 0 : ℤ) : ℂ) * z + ((g₀ 1 1 : ℤ) : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hne
      rw [norm_denom_sq g₀ hz, norm_div, norm_one, norm_pow]
      field_simp
    refine le_trans (mul_le_mul (hC _) (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_imCLM_comp_toSpanSingleton_le _)
        (inv_pos.mpr hwpos).le) (inv_pos.mpr hlog).le) (by positivity) hC0) (le_of_eq ?_)
    rw [hprod]
    field_simp
  · have hev : heightCutoff T =ᶠ[𝓝 z] fun _ => (1 : ℝ) :=
      heightCutoff_eventually_one hT hz (not_lt.mp h1)
    rw [hev.fderiv_eq, fderiv_const_apply, norm_zero]
    positivity

/-- The bound in the form used by the Hodge step: `|Im z · ∂̄θ_T(z)| ≤ C / log T`. -/
theorem exists_norm_im_mul_dbar_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 < T → ∀ z ∈ U,
    ‖(z.im : ℂ) * HodgePair.dbar (fun w => (heightCutoff T w : ℂ)) z‖ ≤ C / Real.log T := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fderiv_heightCutoff_le
  refine ⟨C, hC0, fun T hT z hz => ?_⟩
  have hy : 0 < z.im := hz
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hdiff : DifferentiableAt ℝ (heightCutoff T) z :=
    ((contDiffOn_heightCutoff hT).differentiableOn (by simp)).differentiableAt
      (isOpen_U.mem_nhds hz)
  have hcomp : fderiv ℝ (fun w => (heightCutoff T w : ℂ)) z =
      Complex.ofRealCLM.comp (fderiv ℝ (heightCutoff T) z) :=
    (Complex.ofRealCLM.hasFDerivAt.comp z hdiff.hasFDerivAt).fderiv
  have hbound : ∀ v : ℂ, ‖fderiv ℝ (fun w => (heightCutoff T w : ℂ)) z v‖ ≤
      ‖fderiv ℝ (heightCutoff T) z‖ * ‖v‖ := by
    intro v
    rw [hcomp, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real]
    exact (fderiv ℝ (heightCutoff T) z).le_opNorm v
  have hdbar : ‖HodgePair.dbar (fun w => (heightCutoff T w : ℂ)) z‖ ≤
      ‖fderiv ℝ (heightCutoff T) z‖ := by
    rw [HodgePair.dbar, norm_mul]
    have h1 := hbound 1
    have h2 := hbound Complex.I
    rw [norm_one, mul_one] at h1
    rw [Complex.norm_I, mul_one] at h2
    have h3 : ‖fderiv ℝ (fun w => (heightCutoff T w : ℂ)) z 1 +
        Complex.I * fderiv ℝ (fun w => (heightCutoff T w : ℂ)) z Complex.I‖ ≤
          2 * ‖fderiv ℝ (heightCutoff T) z‖ := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_I, one_mul]
      linarith
    have h4 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h4]
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  calc z.im * ‖HodgePair.dbar (fun w => (heightCutoff T w : ℂ)) z‖
      ≤ z.im * (C / (Real.log T * z.im)) :=
        mul_le_mul_of_nonneg_left (le_trans hdbar (hC T hT z hz)) hy.le
    _ = C / Real.log T := by field_simp

end TernaryPeriodPolynomials.Argument.ESFoundations.Height
