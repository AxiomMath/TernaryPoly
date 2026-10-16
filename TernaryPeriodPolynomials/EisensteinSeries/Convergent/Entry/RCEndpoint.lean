module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.LevelStatements
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarConvergence

@[expose] public section


/-!
# R-c: the standard endpoint integral in degree `n ≥ 4`

For `n ≥ 4` the cohomological point `s₀ = -3/2` lies in the half plane `-n/2 < Re s` on which the
standard integral of a flat family converges absolutely and is analytic
(`CompactScalarConvergence.standard_integrable`, `standard_analyticAt`). A standard family `J` is
meromorphic on that half plane and equals the integral on a right half plane
(`IsStandardConvergent`), so by the identity theorem for meromorphic functions on the connected
half plane the difference has infinite order at every point. At `s₀`, where `J` is analytic, it
therefore equals the integral (`standardEndpointIntegral`).

The degree bound is necessary for this route: for `n ≤ 3` the point `s₀` lies outside the half
plane of absolute convergence. The class-level comparison
consumes `StandardEndpointIntegral n` only for `n ≥ 4` (the plane source data carries `4 ≤ n`).

Written by Claude Opus 5.5.
-/

open MeasureTheory Filter Topology GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem cohomologicalPoint_mem_halfPlane {n : ℕ} (hn : 4 ≤ n) :
    -(n : ℝ) / 2 < cohomologicalPoint.re := by
  have h : (4 : ℝ) ≤ n := by exact_mod_cast hn
  rw [cohomologicalPoint]
  norm_num
  linarith

/-- The identity theorem used for R-c: a function meromorphic on a preconnected open set that
agrees with an analytic function on a nonempty open subset agrees with it at every point where it
is analytic. -/
theorem eq_of_meromorphicOn_of_eqOn_open {U W : Set ℂ} (hU : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : MeromorphicOn f U) (hg : AnalyticOnNhd ℂ g U)
    (hWo : IsOpen W) (hWU : W ⊆ U) {p : ℂ} (hp : p ∈ W) (heq : Set.EqOn f g W)
    {s : ℂ} (hs : s ∈ U) (hfs : AnalyticAt ℂ f s) : f s = g s := by
  have hm : MeromorphicOn (f - g) U := hf.sub fun x hx => (hg x hx).meromorphicAt
  have hp_top : meromorphicOrderAt (f - g) p = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have : ∀ᶠ z in 𝓝 p, (f - g) z = 0 := by
      filter_upwards [hWo.mem_nhds hp] with z hz
      simp [heq hz]
    exact this.filter_mono nhdsWithin_le_nhds
  have hs_top : meromorphicOrderAt (f - g) s = ⊤ := by
    by_contra h
    exact hm.meromorphicOrderAt_ne_top_of_isPreconnected hU hs (hWU hp) h hp_top
  rw [meromorphicOrderAt_eq_top_iff] at hs_top
  have hcont : ContinuousAt (f - g) s := (hfs.sub (hg s hs)).continuousAt
  have hlim : Tendsto (f - g) (𝓝[≠] s) (𝓝 ((f - g) s)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto (f - g) (𝓝[≠] s) (𝓝 0) := tendsto_const_nhds.congr' (by
    filter_upwards [hs_top] with z hz
    exact hz.symm)
  have := tendsto_nhds_unique hlim hlim0
  simpa [sub_eq_zero] using this

/-- **R-c** in degree `n ≥ 4`. -/
theorem standardEndpointIntegral {n : ℕ} (hn : 4 ≤ n) : StandardEndpointIntegral n := by
  intro D F J hflat hconv hana x g m
  set Fc : ℂ → AdelicGL → ℂ := fun s g' => (F s x g').val.coeff m with hFc
  have hs₀ := cohomologicalPoint_mem_halfPlane hn
  refine ⟨CompactScalarConvergence.standard_integrable D Fc (hflat x m) _ hs₀ g, ?_⟩
  obtain ⟨hmer, R, hR⟩ := hconv x m
  set U : Set ℂ := {s : ℂ | -(n : ℝ) / 2 < s.re}
  set W : Set ℂ := {s : ℂ | max R (-(n : ℝ) / 2) < s.re}
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  have hWo : IsOpen W := isOpen_lt continuous_const Complex.continuous_re
  have hWU : W ⊆ U := fun s (hs : _ < _) =>
    (show -(n : ℝ) / 2 < s.re from lt_of_le_of_lt (le_max_right _ _) hs)
  have hp : ((max R (-(n : ℝ) / 2) + 1 : ℝ) : ℂ) ∈ W := by
    show max R (-(n : ℝ) / 2) < ((max R (-(n : ℝ) / 2) + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    linarith
  have hg : AnalyticOnNhd ℂ
      (fun s => ∫ u, standardIntegrand Fc s g u ∂radicalMeasure) U :=
    fun s hs => CompactScalarConvergence.standard_analyticAt D Fc (hflat x m) s hs g
  have heq : Set.EqOn (fun s => (J s x g).val.coeff m)
      (fun s => ∫ u, standardIntegrand Fc s g u ∂radicalMeasure) W :=
    fun s hs => (hR s (lt_of_le_of_lt (le_max_left _ _) hs) g).2
  exact eq_of_meromorphicOn_of_eqOn_open hUc (fun s hs => hmer g s hs) hg hWo hWU hp heq hs₀
    (hana x g m)

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
