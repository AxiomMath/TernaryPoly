module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.ChartGeometry
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricContinuousBilinear
public import TernaryPeriodPolynomials.Analysis.Compact.SmoothCutoff
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

@[expose] public section


/-! # General coercivity, Tier B: smoothing a Lipschitz function with its sharp Riemannian slope

A Lipschitz function of the covering space, composed with the global coordinate chart, can be
mollified in the Euclidean sense on a compact subset of the chart, with the invariant gradient of the
mollification bounded by `(1 + δ)` times the Lipschitz constant.  This uses the length of straight
chart segments and the uniform comparison of the metric at nearby points of a compact set.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceTraceMetric
  TernaryPoly.SymmetricSpaceRiemannian Set Metric Filter
open scoped ContDiff Topology

theorem continuousOn_coordinateBilin_pos :
    ContinuousOn coordinateContinuousBilin positiveCoordinates :=
  contDiffOn_coordinateContinuousBilin.continuousOn

/-- Uniform positivity of the metric on a compact subset of the positive coordinates. -/
theorem exists_pair_lower_bound {C : Set Coordinates} (hC : IsCompact C)
    (hCp : C ⊆ positiveCoordinates) :
    ∃ l : ℝ, 0 < l ∧ ∀ x ∈ C, ∀ v : Coordinates, l * ‖v‖ ^ 2 ≤ coordinatePair x v v := by
  by_cases hne : C.Nonempty
  · have hS : IsCompact (sphere (0 : Coordinates) 1) := isCompact_sphere 0 1
    have hK : IsCompact (C ×ˢ sphere (0 : Coordinates) 1) := hC.prod hS
    have hf : ContinuousOn (fun p : Coordinates × Coordinates => coordinatePair p.1 p.2 p.2)
        (C ×ˢ sphere (0 : Coordinates) 1) := by
      have h1 := contDiffOn_coordinatePair.continuousOn
      have h2 : Continuous (fun p : Coordinates × Coordinates => (p.1, p.2, p.2)) :=
        continuous_fst.prodMk (continuous_snd.prodMk continuous_snd)
      have hm : MapsTo (fun p : Coordinates × Coordinates => (p.1, p.2, p.2))
          (C ×ˢ sphere (0 : Coordinates) 1)
          {q : Coordinates × Coordinates × Coordinates | q.1 ∈ positiveCoordinates} :=
        fun p hp => hCp hp.1
      have h3 := h1.comp h2.continuousOn hm
      exact h3
    have hSne : (sphere (0 : Coordinates) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
    obtain ⟨p0, hp0, hmin⟩ := hK.exists_isMinOn (hne.prod hSne) hf
    have hpos : 0 < coordinatePair p0.1 p0.2 p0.2 := by
      apply coordinatePair_pos p0.1 (hCp hp0.1) p0.2
      intro h0
      have := hp0.2
      rw [h0] at this
      simp at this
    refine ⟨coordinatePair p0.1 p0.2 p0.2, hpos, fun x hx v => ?_⟩
    by_cases hv : v = 0
    · have h0 : coordinatePair x 0 0 = 0 := by
        rw [← coordinateContinuousBilin_apply]
        simp
      rw [hv, h0]
      simp
    · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hu : (‖v‖⁻¹ • v) ∈ sphere (0 : Coordinates) 1 := by
        simp [norm_smul, hvn.ne']
      have h1 := hmin (show (x, ‖v‖⁻¹ • v) ∈ C ×ˢ sphere (0 : Coordinates) 1 from ⟨hx, hu⟩)
      have h2 : coordinatePair p0.1 p0.2 p0.2 ≤ coordinatePair x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := h1
      have hscale : coordinatePair x v v =
          ‖v‖ ^ 2 * coordinatePair x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := by
        rw [← coordinateContinuousBilin_apply, ← coordinateContinuousBilin_apply]
        simp only [map_smul, smul_apply, smul_eq_mul]
        field_simp
      rw [hscale]
      nlinarith [sq_nonneg ‖v‖]
  · refine ⟨1, one_pos, fun x hx => (hne ⟨x, hx⟩).elim⟩

/-- Uniform comparison of the metric at nearby points of a compact set. -/
theorem exists_metric_comparison {C : Set Coordinates} (hC : IsCompact C)
    (hCp : C ⊆ positiveCoordinates) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ cthickening r C ⊆ positiveCoordinates ∧ ∀ x ∈ C, ∀ y : Coordinates,
      dist y x < r → ∀ v : Coordinates,
        Real.sqrt (coordinatePair y v v) ≤ (1 + δ) * Real.sqrt (coordinatePair x v v) := by
  obtain ⟨ρ0, hρ0, hcth⟩ := hC.exists_cthickening_subset_open isOpen_positiveCoordinates hCp
  have hC1 : IsCompact (cthickening ρ0 C) := hC.cthickening
  have hcont : ContinuousOn coordinateContinuousBilin (cthickening ρ0 C) :=
    continuousOn_coordinateBilin_pos.mono hcth
  have huc : UniformContinuousOn coordinateContinuousBilin (cthickening ρ0 C) :=
    hC1.uniformContinuousOn_of_continuous hcont
  obtain ⟨l, hl, hlow⟩ := exists_pair_lower_bound hC hCp
  have hη : 0 < l * ((1 + δ) ^ 2 - 1) := mul_pos hl (by nlinarith)
  have hmet := @Metric.uniformContinuousOn_iff Coordinates
    (Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ) _ _ coordinateContinuousBilin (cthickening ρ0 C)
  obtain ⟨ρ, hρ, hρc⟩ := hmet.mp huc _ hη
  refine ⟨min ρ0 ρ, lt_min hρ0 hρ, (cthickening_mono (min_le_left _ _) C).trans hcth, ?_⟩
  intro x hx y hy v
  have hy1 : y ∈ cthickening ρ0 C := mem_cthickening_of_dist_le y x ρ0 C hx
    ((hy.trans_le (min_le_left _ _)).le)
  have hx1 : x ∈ cthickening ρ0 C := self_subset_cthickening C hx
  have hd := hρc y hy1 x hx1 (hy.trans_le (min_le_right _ _))
  have hd' : ‖coordinateContinuousBilin y - coordinateContinuousBilin x‖ <
      l * ((1 + δ) ^ 2 - 1) := by
    calc ‖coordinateContinuousBilin y - coordinateContinuousBilin x‖
        = dist (coordinateContinuousBilin y) (coordinateContinuousBilin x) :=
          (dist_eq_norm (coordinateContinuousBilin y) (coordinateContinuousBilin x)).symm
      _ < _ := hd
  have h1 : coordinatePair y v v ≤ coordinatePair x v v + l * ((1 + δ) ^ 2 - 1) * ‖v‖ ^ 2 := by
    have e : coordinatePair y v v = coordinatePair x v v +
        ((coordinateContinuousBilin y - coordinateContinuousBilin x) v) v := by
      simp only [← coordinateContinuousBilin_apply, sub_apply]
      ring
    rw [e]
    have h2 := ContinuousLinearMap.le_opNorm₂ (coordinateContinuousBilin y - coordinateContinuousBilin x) v v
    have h3 : ((coordinateContinuousBilin y - coordinateContinuousBilin x) v) v ≤
        l * ((1 + δ) ^ 2 - 1) * ‖v‖ ^ 2 := by
      calc _ ≤ ‖((coordinateContinuousBilin y - coordinateContinuousBilin x) v) v‖ := le_abs_self _
        _ ≤ ‖coordinateContinuousBilin y - coordinateContinuousBilin x‖ * ‖v‖ * ‖v‖ := h2
        _ ≤ l * ((1 + δ) ^ 2 - 1) * ‖v‖ * ‖v‖ := by
          have := hd'.le
          gcongr
        _ = _ := by ring
    linarith
  have h4 : l * ‖v‖ ^ 2 ≤ coordinatePair x v v := hlow x hx v
  have h5 : coordinatePair y v v ≤ (1 + δ) ^ 2 * coordinatePair x v v := by
    have : l * ((1 + δ) ^ 2 - 1) * ‖v‖ ^ 2 ≤ ((1 + δ) ^ 2 - 1) * coordinatePair x v v := by
      have := mul_le_mul_of_nonneg_left h4 (show 0 ≤ (1 + δ) ^ 2 - 1 by nlinarith)
      linarith
    nlinarith
  calc Real.sqrt (coordinatePair y v v) ≤ Real.sqrt ((1 + δ) ^ 2 * coordinatePair x v v) :=
        Real.sqrt_le_sqrt h5
    _ = (1 + δ) * Real.sqrt (coordinatePair x v v) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]

attribute [local instance] spaceMetricSpace in
/-- Lipschitz functions of the covering space are sharply Lipschitz in adapted coordinates. -/
theorem lipschitz_chart_sharp {C : Set Coordinates} {r : ℝ}
    (hcth : cthickening r C ⊆ positiveCoordinates) {δ : ℝ}
    (hcmp : ∀ x ∈ C, ∀ y : Coordinates, dist y x < r → ∀ v : Coordinates,
      Real.sqrt (coordinatePair y v v) ≤ (1 + δ) * Real.sqrt (coordinatePair x v v))
    {m : Space → ℝ} {L : ℝ} (hL : 0 ≤ L) (hm : ∀ S T, |m S - m T| ≤ L * dist S T) {x : Coordinates}
    (hx : x ∈ C) {a b : Coordinates} (ha : dist a x < r) (hb : dist b x < r) :
    |m (coordinateChart.symm a) - m (coordinateChart.symm b)| ≤
      L * ((1 + δ) * Real.sqrt (coordinatePair x (b - a) (b - a))) := by
  have hball : ∀ t ∈ Icc (0 : ℝ) 1, dist (AffineMap.lineMap a b t) x < r := by
    intro t ht
    have : AffineMap.lineMap a b t ∈ Metric.ball x r :=
      (convex_ball x r).segment_subset (Metric.mem_ball.mpr ha) (Metric.mem_ball.mpr hb)
        (by rw [segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩)
    exact Metric.mem_ball.mp this
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap a b t ∈ positiveCoordinates := fun t ht =>
    hcth (mem_cthickening_of_dist_le _ x r C hx (hball t ht).le)
  have hd := dist_chart_le hseg (B := (1 + δ) * Real.sqrt (coordinatePair x (b - a) (b - a)))
    (fun t ht => hcmp x hx _ (hball t ht) (b - a))
  exact (hm _ _).trans (mul_le_mul_of_nonneg_left hd hL)

section Mollify

open MeasureTheory
open scoped Convolution

/-- Euclidean mollification of a function with a sharp local Lipschitz bound keeps the bound. -/
theorem exists_mollified_slope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {M : E → ℝ} (hM : Continuous M) (hMc : HasCompactSupport M)
    {C : Set E} {r : ℝ} (hr : 0 < r) {Q : E → E → ℝ}
    (hQ1 : ∀ x ∈ C, ∀ a b : E, dist a x < r → dist b x < r → |M a - M b| ≤ Q x (b - a))
    (hQ2 : ∀ x ∈ C, ∀ (w : E) (s : ℝ), 0 ≤ s → Q x (s • w) = s * Q x w) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ (∀ x ∈ C, |g x - M x| ≤ δ) ∧
      ∀ x ∈ C, ∀ v : E, |fderiv ℝ g x v| ≤ Q x v := by
  have huc : UniformContinuous M := HasCompactSupport.uniformContinuous_of_continuous hMc hM
  obtain ⟨ε1, hε1, hM1⟩ := Metric.uniformContinuous_iff.mp huc δ hδ
  let ε : ℝ := min (r / 2) ε1
  have hε : 0 < ε := lt_min (half_pos hr) hε1
  let φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  let g : E → ℝ := φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] M
  have hgs : ContDiff ℝ ∞ g :=
    (φ.hasCompactSupport_normed (μ := μ)).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ.contDiff_normed (μ := μ)) (hM.locallyIntegrable (μ := μ))
  have hconv : ∀ z : E, g z = ∫ t, φ.normed μ t * M (z - t) ∂μ := fun z => by
    simp only [g, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hint : ∀ z : E, Integrable (fun t => φ.normed μ t * M (z - t)) μ := fun z => by
    have := (φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ.continuous_normed (μ := μ)) (hM.locallyIntegrable (μ := μ)) z
    exact this
  refine ⟨g, hgs, ?_, ?_⟩
  · intro x hx
    have := φ.dist_normed_convolution_le (μ := μ) hM.aestronglyMeasurable (x₀ := x) (ε := δ)
      (fun y hy => (hM1 (Metric.mem_ball.mp hy |>.trans_le (min_le_right _ _))).le)
    exact (Real.dist_eq _ _) ▸ this
  · intro x hx v
    have hkey : ∀ s : ℝ, 0 < s → s * ‖v‖ < r / 2 → |g (x + s • v) - g x| ≤ s * Q x v := by
      intro s hs hsv
      have e : g (x + s • v) - g x =
          ∫ t, φ.normed μ t * (M (x + s • v - t) - M (x - t)) ∂μ := by
        rw [hconv, hconv, ← integral_sub (hint _) (hint _)]
        congr 1
        funext t
        ring
      have hb : ∀ t, ‖φ.normed μ t * (M (x + s • v - t) - M (x - t))‖ ≤
          φ.normed μ t * (s * Q x v) := by
        intro t
        by_cases ht : φ.normed μ t = 0
        · simp [ht]
        · have hsupp : t ∈ Metric.ball (0 : E) φ.rOut := by
            rw [← φ.support_normed_eq (μ := μ)]
            exact ht
          have htε : ‖t‖ < ε := by simpa using hsupp
          have htr : ‖t‖ < r / 2 := htε.trans_le (min_le_left _ _)
          have h1 : dist (x - t) x < r := by
            rw [dist_eq_norm]; simp only [sub_sub_cancel_left, norm_neg]; linarith
          have h2 : dist (x + s • v - t) x < r := by
            rw [dist_eq_norm]
            have : x + s • v - t - x = s • v - t := by abel
            rw [this]
            calc ‖s • v - t‖ ≤ ‖s • v‖ + ‖t‖ := norm_sub_le _ _
              _ = s * ‖v‖ + ‖t‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
              _ < r := by linarith
          have h3 := hQ1 x hx _ _ h1 h2
          have h4 : x + s • v - t - (x - t) = s • v := by abel
          rw [h4, hQ2 x hx v s hs.le] at h3
          rw [norm_mul, Real.norm_of_nonneg (φ.nonneg_normed t), Real.norm_eq_abs]
          have := abs_sub_comm (M (x - t)) (M (x + s • v - t))
          exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact h3) (φ.nonneg_normed t)
      rw [e, ← Real.norm_eq_abs]
      calc ‖∫ t, φ.normed μ t * (M (x + s • v - t) - M (x - t)) ∂μ‖
          ≤ ∫ t, φ.normed μ t * (s * Q x v) ∂μ :=
            norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _) (Eventually.of_forall hb)
        _ = s * Q x v := by rw [integral_mul_const, φ.integral_normed, one_mul]
    have hd : HasDerivAt (fun s : ℝ => g (x + s • v)) (fderiv ℝ g x v) 0 := by
      have h1 : HasFDerivAt g (fderiv ℝ g x) (x + (0 : ℝ) • v) := by
        simpa using (hgs.differentiable (by simp) x).hasFDerivAt
      have h2 : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      exact h1.comp_hasDerivAt (0 : ℝ) h2
    have hslope := hd.tendsto_slope_zero_right
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), |s⁻¹ • (g (x + (0 + s) • v) - g (x + (0 : ℝ) • v))| ≤ Q x v := by
      have hpos : 0 < r / 2 / (‖v‖ + 1) := by positivity
      filter_upwards [Ioo_mem_nhdsGT hpos] with s hs
      have hs0 : 0 < s := hs.1
      have hsv : s * ‖v‖ < r / 2 := by
        have : s * (‖v‖ + 1) < r / 2 := by
          have := hs.2
          rw [lt_div_iff₀ (by positivity)] at this
          exact this
        nlinarith [norm_nonneg v]
      have := hkey s hs0 hsv
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hs0]
      rw [inv_mul_le_iff₀ hs0]
      linarith
    exact le_of_tendsto hslope.abs hev

end Mollify

attribute [local instance] spaceMetricSpace in
/-- **Smoothing with the sharp Riemannian slope.**  A Lipschitz function of the covering space can be
approximated, on a compact set of the chart, by a smooth function whose invariant gradient is at most
`(1 + δ)` times the Lipschitz constant. -/
theorem exists_smooth_slope {C : Set Coordinates} (hC : IsCompact C)
    (hCp : C ⊆ positiveCoordinates) {m : Space → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hm : ∀ S T, |m S - m T| ≤ L * dist S T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : Coordinates → ℝ, ContDiff ℝ ∞ g ∧
      (∀ x ∈ C, |g x - m (coordinateChart.symm x)| ≤ δ) ∧
      ∀ x ∈ C, ∀ v : Coordinates,
        |fderiv ℝ g x v| ≤ (1 + δ) * L * Real.sqrt (coordinatePair x v v) := by
  obtain ⟨r, hr, hcth, hcmp⟩ := exists_metric_comparison hC hCp hδ
  have hKc : IsCompact (cthickening r C) := hC.cthickening
  obtain ⟨θ, hθ, hθc, hθs, hθ1⟩ := TernaryPoly.CompactSmoothCutoff.exists_cutoff hKc
    isOpen_positiveCoordinates hcth
  have hθ1' : ∀ y ∈ cthickening r C, θ y = 1 := fun y hy => (hθ1 y hy).self_of_nhds
  let M : Coordinates → ℝ := fun y => θ y * m (coordinateChart.symm y)
  have hmLip : LipschitzWith (Real.toNNReal L) m :=
    LipschitzWith.of_dist_le_mul fun S T => by
      simpa [Real.dist_eq, Real.coe_toNNReal _ hL] using hm S T
  have hmc : Continuous m := hmLip.continuous
  have hMc : Continuous M := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ positiveCoordinates
    · have h1 : ContinuousAt (fun y => m (coordinateChart.symm y)) y :=
        hmc.continuousAt.comp (coordinateChart.continuousAt_symm (by rw [coordinateChart_target]; exact hy))
      exact hθ.continuous.continuousAt.mul h1
    · have : y ∉ tsupport θ := fun h => hy (hθs h)
      have h0 : θ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp this
      have : M =ᶠ[𝓝 y] 0 := by
        filter_upwards [h0] with z hz
        simp [M, hz]
      exact (continuousAt_const.congr this.symm)
  have hMcs : HasCompactSupport M :=
    hθc.mono' (fun y hy => subset_tsupport θ (left_ne_zero_of_mul hy))
  have hMeq : ∀ y ∈ cthickening r C, M y = m (coordinateChart.symm y) := fun y hy => by
    simp [M, hθ1' y hy]
  have hQ1 : ∀ x ∈ C, ∀ a b : Coordinates, dist a x < r → dist b x < r →
      |M a - M b| ≤ (fun x w => (1 + δ) * L * Real.sqrt (coordinatePair x w w)) x (b - a) := by
    intro x hx a b ha hb
    have ha' : a ∈ cthickening r C := mem_cthickening_of_dist_le a x r C hx ha.le
    have hb' : b ∈ cthickening r C := mem_cthickening_of_dist_le b x r C hx hb.le
    rw [hMeq a ha', hMeq b hb']
    have := lipschitz_chart_sharp hcth hcmp hL hm hx ha hb
    exact this.trans_eq (by ring)
  have hQ2 : ∀ x ∈ C, ∀ (w : Coordinates) (s : ℝ), 0 ≤ s →
      (fun x w => (1 + δ) * L * Real.sqrt (coordinatePair x w w)) x (s • w) =
        s * (fun x w => (1 + δ) * L * Real.sqrt (coordinatePair x w w)) x w := by
    intro x hx w s hs
    have h1 : coordinatePair x (s • w) (s • w) = s ^ 2 * coordinatePair x w w := by
      rw [← coordinateContinuousBilin_apply, ← coordinateContinuousBilin_apply]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    simp only [h1, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]
    ring
  obtain ⟨g, hg, hgM, hgs⟩ := exists_mollified_slope (μ := MeasureTheory.volume) (C := C)
    (Q := fun x w => (1 + δ) * L * Real.sqrt (coordinatePair x w w)) hMc hMcs hr hQ1 hQ2 hδ
  refine ⟨g, hg, fun x hx => ?_, hgs⟩
  have := hgM x hx
  rwa [hMeq x (self_subset_cthickening C hx)] at this

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
