module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Compact.PowerSeriesIntegral

@[expose] public section


/-!
# Real analyticity of a parametric interval integral

`analyticAt_param_integral`: if `Φ : ℝ × Q → H` is jointly real analytic at `(s, q₀)` for every `s ∈ [0, 1]`
(`Q`, `H` real normed spaces, `H` complete), then `q ↦ ∫₀¹ Φ(s, q) ds` is real analytic at `q₀`.  This is the
analytic (`ContDiffOn ℝ ω`) parametric integral that the smoothness clauses of the induced sections need (the library's
`Smooth` is `ContDiffOn ℝ ⊤`, i.e. real analytic).  The proof covers `[0,1]` by finitely many subintervals each inside
one power-series ball of `Φ` (Lebesgue number), re-expands each ball series at the points of its subinterval
(`HasFPowerSeriesOnBall.changeOrigin`, with the uniform bounds `changeOrigin_bound`), and integrates the slice series
with `compactPowerSeriesIntegral_analyticAt`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal unitInterval

open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

variable {Q H : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup H]
  [NormedSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Uniform bounds on the change-of-origin coefficients. -/
theorem changeOrigin_bound (p : FormalMultilinearSeries ℝ (ℝ × Q) H) {ρ r' : ℝ≥0}
    (h : (ρ + r' : ℝ≥0∞) < p.radius) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
      (∀ y : ℝ × Q, ‖y‖₊ ≤ ρ → ∀ k, ‖p.changeOrigin y k‖ ≤ B k) ∧
      Summable (fun k => B k * (r' : ℝ) ^ k) := by
  have hρ : (ρ : ℝ≥0∞) < p.radius := lt_of_le_of_lt le_self_add h
  set T : ℕ → ℝ≥0 := fun k => ∑' s : Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l },
    ‖p (k + s.1)‖₊ * ρ ^ s.1 with hT
  refine ⟨fun k => (T k : ℝ), fun k => (T k).coe_nonneg, fun y hy k => ?_, ?_⟩
  · have hy' : (‖y‖₊ : ℝ≥0∞) < p.radius := lt_of_le_of_lt (by exact_mod_cast hy) hρ
    have h1 := p.nnnorm_changeOrigin_le k hy'
    have hs := p.changeOriginSeries_summable_aux₂ hρ k
    have h2 : (∑' s : Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l },
        ‖p (k + s.1)‖₊ * ‖y‖₊ ^ s.1) ≤ T k := by
      refine Summable.tsum_le_tsum (fun s => ?_) (NNReal.summable_of_le (fun s => ?_) hs) hs
      · gcongr
      · gcongr
    have h3 : ‖p.changeOrigin y k‖₊ ≤ T k := h1.trans h2
    exact_mod_cast h3
  · have hsum := (NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ h)).2
    have : Summable (fun k : ℕ => T k * r' ^ k) := by
      refine hsum.congr (fun k => ?_)
      rw [hT]
      simp only []
      rw [← NNReal.tsum_mul_right]
    have := NNReal.summable_coe.mpr this
    simpa using this



theorem seg_mem' (N i : ℕ) (hi : i < N) :
    ((i : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 ∧ ((i : ℝ) + 1) / N ∈ Set.Icc (0 : ℝ) 1) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hi)
  have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  exact ⟨⟨by positivity, (div_le_one hN).mpr (by linarith)⟩, ⟨by positivity, (div_le_one hN).mpr hi'⟩⟩

omit [CompleteSpace H] in
theorem integral_unit (f : ℝ → H) : ∫ t : I, f t ∂(volume : Measure I) = ∫ t in (0:ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Icc f

theorem analyticAt_integral_piece (Ψ : ℝ × Q → H) (p : FormalMultilinearSeries ℝ (ℝ × Q) H) (c : ℝ)
    (r : ℝ≥0∞) (hp : HasFPowerSeriesOnBall Ψ p (c, 0) r) (u w : ℝ) (ρ : ℝ≥0)
    (hρ : (ρ : ℝ≥0∞) < r) (hu : |u - c| ≤ ρ) (hw : |w - c| ≤ ρ) :
    AnalyticAt ℝ (fun b : Q => ∫ s in u..w, Ψ (s, b)) 0 := by
  obtain ⟨r', hr'pos, hρr'⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hρ
  have hrad : (ρ + r' : ℝ≥0∞) < p.radius := lt_of_lt_of_le hρr' hp.r_le
  have hρrad : (ρ : ℝ≥0∞) < p.radius := lt_of_le_of_lt le_self_add hrad
  obtain ⟨B, hB0, hBb, hBs⟩ := changeOrigin_bound p hrad
  set s : I → ℝ := fun t => u + (t : ℝ) * (w - u) with hsdef
  have hs : ∀ t : I, |s t - c| ≤ ρ := by
    intro t
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have e : s t - c = (1 - (t : ℝ)) * (u - c) + (t : ℝ) * (w - c) := by simp only [hsdef]; ring
    rw [e]
    calc |(1 - (t : ℝ)) * (u - c) + (t : ℝ) * (w - c)|
        ≤ |(1 - (t : ℝ)) * (u - c)| + |(t : ℝ) * (w - c)| := abs_add_le _ _
      _ = (1 - (t : ℝ)) * |u - c| + (t : ℝ) * |w - c| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - (t : ℝ)), abs_of_nonneg ht0]
      _ ≤ (1 - (t : ℝ)) * ρ + (t : ℝ) * ρ := by gcongr
      _ = ρ := by ring
  set y : I → ℝ × Q := fun t => (s t - c, 0) with hydef
  have hy : ∀ t, ‖y t‖₊ ≤ ρ := by
    intro t
    have : ‖y t‖₊ = ‖s t - c‖₊ := by simp [hydef, Prod.nnnorm_def]
    rw [this]
    have := hs t
    rw [← NNReal.coe_le_coe]
    simpa using this
  have hycont : Continuous y := by
    refine Continuous.prodMk ?_ continuous_const
    simp only [hsdef]
    fun_prop
  let coef : I → FormalMultilinearSeries ℝ Q H := fun t m =>
    (p.changeOrigin (y t) m).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ ℝ Q)
  have hmem : ∀ t, y t ∈ Metric.eball (0 : ℝ × Q) p.radius := by
    intro t
    rw [Metric.mem_eball, edist_zero_right]
    exact lt_of_le_of_lt (by exact_mod_cast hy t) hρrad
  have hcont : ∀ m (v : Fin m → Q), Continuous (fun t : I => coef t m v) := by
    intro m v
    have h1 : ContinuousOn (fun x : ℝ × Q => p.changeOrigin x m) (Metric.eball 0 p.radius) :=
      (p.hasFPowerSeriesOnBall_changeOrigin m (lt_of_le_of_lt (bot_le : (0:ℝ≥0∞) ≤ ρ) hρrad)).continuousOn
    have h2 : Continuous (fun t : I => p.changeOrigin (y t) m) :=
      h1.comp_continuous hycont hmem
    have h3 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℝ × Q) H
      (fun i => ContinuousLinearMap.inr ℝ ℝ Q (v i))).continuous.comp h2
    exact h3
  have hbound : ∀ t m, ‖coef t m‖ ≤ B m := by
    intro t m
    calc ‖coef t m‖ ≤ ‖p.changeOrigin (y t) m‖ * ∏ _i : Fin m, ‖ContinuousLinearMap.inr ℝ ℝ Q‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖p.changeOrigin (y t) m‖ * 1 := by
          gcongr
          exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ ℝ Q)
      _ ≤ B m := by rw [mul_one]; exact hBb _ (hy t) m
  have hexp : ∀ (t : I) (b : Q), ‖b‖ < r' → HasSum (fun m => coef t m (fun _ => b)) (Ψ (s t, b)) := by
    intro t b hb
    have hyr : (‖y t‖₊ : ℝ≥0∞) < r := lt_of_le_of_lt (by exact_mod_cast hy t) hρ
    have hco := hp.changeOrigin hyr
    have hbmem : ((0 : ℝ), b) ∈ Metric.eball (0 : ℝ × Q) (r - ‖y t‖₊) := by
      rw [Metric.mem_eball, edist_zero_right, lt_tsub_iff_right]
      have h1 : (‖((0 : ℝ), b)‖ₑ : ℝ≥0∞) = ‖b‖₊ := by
        rw [enorm_eq_nnnorm, Prod.nnnorm_def]; simp
      rw [h1]
      have hbn : (‖b‖₊ : ℝ≥0∞) < r' := by exact_mod_cast hb
      calc (‖b‖₊ : ℝ≥0∞) + ‖y t‖₊ ≤ r' + ρ := add_le_add hbn.le (by exact_mod_cast hy t)
        _ = ρ + r' := add_comm _ _
        _ < r := hρr'
    have := hco.hasSum hbmem
    have e : ((c, (0 : Q)) + y t + ((0 : ℝ), b)) = (s t, b) := by
      simp [hydef]
    rw [e] at this
    exact this
  have key := compactPowerSeriesIntegral_analyticAt (X := I) (E := Q) (F := H)
    (volume : Measure I) coef (fun t b => Ψ (s t, b)) hcont B hB0 hbound r' hr'pos hBs hexp
  have hfun : (fun b : Q => ∫ x in u..w, Ψ (x, b)) =
      fun b => (w - u) • ∫ t, Ψ (s t, b) ∂(volume : Measure I) := by
    funext b
    have h1 := integral_unit (fun x : ℝ => Ψ (u + x * (w - u), b))
    have h2 := intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1) (fun x : ℝ => Ψ (x, b)) (w - u) u
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at h2
    rw [← h2]
    congr 1
    rw [show (∫ t, Ψ (s t, b) ∂(volume : Measure I)) = ∫ t in (0:ℝ)..1, Ψ (u + t * (w - u), b) from h1]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    congr 2
    ring
  rw [hfun]
  exact key.const_smul


theorem analyticAt_integral_unit (Ψ : ℝ × Q → H) (hΨ : ∀ s ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℝ Ψ (s, 0)) :
    AnalyticAt ℝ (fun b : Q => ∫ s in (0 : ℝ)..1, Ψ (s, b)) 0 := by
  classical
  have hdata : ∀ s : Set.Icc (0 : ℝ) 1, ∃ (p : FormalMultilinearSeries ℝ (ℝ × Q) H) (R : ℝ≥0), 0 < R ∧
      HasFPowerSeriesOnBall Ψ p ((s : ℝ), 0) R := by
    intro s
    obtain ⟨p, r, hr⟩ := hΨ s s.2
    obtain ⟨R, hR0, hRr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr.r_pos
    exact ⟨p, R, by exact_mod_cast hR0, hr.mono hR0 hRr.le⟩
  choose p R hR hp using hdata
  -- the Lebesgue number of the cover
  have hcov : Set.Icc (0 : ℝ) 1 ⊆ ⋃ s : Set.Icc (0 : ℝ) 1, Metric.ball (s : ℝ) (R s / 2) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self ?_⟩
    have := hR ⟨x, hx⟩
    positivity
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc (fun _ => Metric.isOpen_ball) hcov
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hNδ : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at hN
    linarith
  -- each piece is analytic
  have hpiece : ∀ j : ℕ, j < N → AnalyticAt ℝ (fun b : Q => ∫ s in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), Ψ (s, b)) 0 := by
    intro j hj
    have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    have ha : (j : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := (seg_mem' N j hj).1
    obtain ⟨s, hs⟩ := hleb _ ha
    have h1 : (j : ℝ) / N ∈ Metric.ball ((j : ℝ) / N) δ := Metric.mem_ball_self hδ
    have h2 : ((j : ℝ) + 1) / N ∈ Metric.ball ((j : ℝ) / N) δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have : ((j : ℝ) + 1) / N - (j : ℝ) / N = 1 / N := by ring
      rw [this, abs_of_pos (by positivity)]
      exact hNδ
    have h1' := hs h1
    have h2' := hs h2
    rw [Metric.mem_ball, Real.dist_eq] at h1' h2'
    have hρ : ((R s / 2 : ℝ≥0) : ℝ≥0∞) < R s := by
      have := hR s
      exact_mod_cast (half_lt_self this)
    refine analyticAt_integral_piece Ψ (p s) (s : ℝ) (R s) (hp s) _ _ (R s / 2) hρ ?_ ?_
    · exact_mod_cast h1'.le
    · exact_mod_cast h2'.le
  -- the continuity needed to split the integral
  have hopen : IsOpen {x : ℝ × Q | AnalyticAt ℝ Ψ x} := isOpen_analyticAt ℝ Ψ
  obtain ⟨U, W, hU, hW, hUs, hW0, hUW⟩ := generalized_tube_lemma (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    (isCompact_singleton (x := (0 : Q))) hopen (by
      rintro ⟨x1, x2⟩ ⟨h1, h2⟩
      rw [Set.mem_singleton_iff] at h2
      simp only at h1 h2
      subst h2
      exact hΨ x1 h1)
  have hWn : W ∈ 𝓝 (0 : Q) := hW.mem_nhds (hW0 rfl)
  have hsplit : ∀ b ∈ W, ∫ s in (0 : ℝ)..1, Ψ (s, b) =
      ∑ j ∈ Finset.range N, ∫ s in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), Ψ (s, b) := by
    intro b hb
    have hcont : ContinuousOn (fun s : ℝ => Ψ (s, b)) (Set.Icc 0 1) := by
      intro s hs
      have h1 : AnalyticAt ℝ Ψ (s, b) := hUW ⟨hUs hs, hb⟩
      have hc : Continuous (fun s : ℝ => (s, b)) := by fun_prop
      exact (ContinuousAt.comp (g := Ψ) (f := fun s : ℝ => (s, b)) h1.continuousAt
        hc.continuousAt).continuousWithinAt
    have := intervalIntegral.sum_integral_adjacent_intervals (f := fun s : ℝ => Ψ (s, b)) (μ := volume)
      (a := fun j : ℕ => (j : ℝ) / N) (n := N) (fun j hj => by
        refine (hcont.mono ?_).intervalIntegrable
        have h := seg_mem' N j hj
        exact Set.uIcc_subset_Icc h.1 (by simpa using h.2))
    have e0 : ((0 : ℕ) : ℝ) / N = 0 := by simp
    have eN : ((N : ℕ) : ℝ) / N = 1 := div_self hNpos.ne'
    simp only [e0, eN] at this
    simpa using this.symm
  have hev : (fun b : Q => ∫ s in (0 : ℝ)..1, Ψ (s, b)) =ᶠ[𝓝 0]
      fun b => ∑ j ∈ Finset.range N, ∫ s in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), Ψ (s, b) :=
    Filter.eventually_of_mem hWn hsplit
  refine AnalyticAt.congr ?_ hev.symm
  exact Finset.analyticAt_fun_sum _ (fun j hj => hpiece j (Finset.mem_range.mp hj))

/-- **Analytic dependence of a parametric interval integral** (compact parameter interval): if `Φ` is jointly real
analytic at `(s, q₀)` for every `s ∈ [0,1]`, then `q ↦ ∫₀¹ Φ(s, q) ds` is real analytic at `q₀`. -/
theorem analyticAt_param_integral (Φ : ℝ × Q → H) (q₀ : Q)
    (hΦ : ∀ s ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℝ Φ (s, q₀)) :
    AnalyticAt ℝ (fun q : Q => ∫ s in (0 : ℝ)..1, Φ (s, q)) q₀ := by
  have hshift : ∀ s : ℝ, AnalyticAt ℝ (fun x : ℝ × Q => (x.1, q₀ + x.2)) (s, 0) := by
    intro s
    exact AnalyticAt.prod (analyticAt_fst) (analyticAt_const.add (analyticAt_snd))
  have h1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℝ (fun x : ℝ × Q => Φ (x.1, q₀ + x.2)) (s, 0) := by
    intro s hs
    exact (hΦ s hs).comp_of_eq (hshift s) (by simp)
  have h2 := analyticAt_integral_unit (fun x : ℝ × Q => Φ (x.1, q₀ + x.2)) h1
  have h3 : AnalyticAt ℝ (fun q : Q => q - q₀) q₀ := analyticAt_id.sub analyticAt_const
  have := AnalyticAt.comp_of_eq h2 h3 (by simp)
  simpa [Function.comp_def] using this

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
