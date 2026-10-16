module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.SupBound

@[expose] public section


/-!
# `Hk 2` functions have continuous representatives

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace ENNReal

section Base

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem norm_mol_diff_le {K : Set ℂ} (hK : IsCompact K) {v g1 h : ℂ → X} (hv : L2s K v)
    (hg1 : WD 1 v g1) (hh : WD 0 g1 h) (hg1L : L2s K g1) (hhL : L2s K h) (n m : ℕ) (z : ℂ) :
    ‖mol n v z - mol m v z‖ ≤ Real.sqrt (volume (cthickening 1 K)).toReal *
      (eLpNorm (fun w => mol n h w - mol m h w) 2 volume).toReal := by
  have hvl : LocallyIntegrable v volume := (hv.integrable hK).locallyIntegrable
  have hg1l : LocallyIntegrable g1 volume := (hg1L.integrable hK).locallyIntegrable
  have c1 := mol_contDiff n hvl
  have c2 := mol_contDiff m hvl
  have hψ : ContDiff ℝ ∞ fun z => mol n v z - mol m v z := c1.sub c2
  have hψk : HasCompactSupport fun z => mol n v z - mol m v z :=
    (mol_hasCompactSupport n hK hv.2).sub (mol_hasCompactSupport m hK hv.2)
  have d1 : ∀ z, fderiv ℝ (fun z => mol n v z - mol m v z) z (dir 1) =
      mol n g1 z - mol m g1 z := fun z => by
    rw [fderiv_fun_sub (c1.differentiable (by simp) z) (c2.differentiable (by simp) z)]
    simp only [sub_apply]
    rw [mol_wd n hg1 hvl z, mol_wd m hg1 hvl z]
  have e1 : (fun z => fderiv ℝ (fun z => mol n v z - mol m v z) z (dir 1)) =
      fun z => mol n g1 z - mol m g1 z := funext d1
  have d2 : ∀ w, fderiv ℝ (fun z => fderiv ℝ (fun z => mol n v z - mol m v z) z (dir 1)) w (dir 0) =
      mol n h w - mol m h w := fun w => by
    rw [e1, fderiv_fun_sub ((mol_contDiff n hg1l).differentiable (by simp) w)
      ((mol_contDiff m hg1l).differentiable (by simp) w)]
    simp only [sub_apply]
    rw [mol_wd n hh hg1l w, mol_wd m hh hg1l w]
  have h1 := norm_le_integral_D01 hψ hψk z
  simp only [d2] at h1
  have hL : L2s (cthickening 1 K) fun w => mol n h w - mol m h w :=
    (L2s_mol n hK hhL).sub (L2s_mol m hK hhL)
  have h2 := integral_norm_le_sqrt hK.cthickening hL
  have e : Real.sqrt (∫ z, ‖mol n h z - mol m h z‖ ^ 2) =
      (eLpNorm (fun w => mol n h w - mol m h w) 2 volume).toReal := by
    rw [eLpNorm_two_eq hL.1, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  rw [e] at h2
  exact h1.trans h2

theorem exists_continuous_of_Hk_two {K : Set ℂ} (hK : IsCompact K) {v : ℂ → X} (hv : Hk K 2 v) :
    ∃ w : ℂ → X, Continuous w ∧ v =ᵐ[volume] w ∧ ∀ z, z ∉ cthickening 1 K → w z = 0 := by
  obtain ⟨hl, g, hg, hgk⟩ := hv
  obtain ⟨hl1, g', hg', hg'k⟩ := hgk 1
  have hhL : L2s K (g' 0) := (hg'k 0).l2s
  have hg1L : L2s K (g 1) := (hgk 1).l2s
  have hvl : LocallyIntegrable v volume := (hl.integrable hK).locallyIntegrable
  have hcau := cauchy_mol hhL.1
  set B := Real.sqrt (volume (cthickening 1 K)).toReal with hB
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hunif : UniformCauchySeqOn (fun n => mol n v) atTop univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hpos : 0 < ε / (B + 1) / 2 := by positivity
    obtain ⟨N, hN⟩ := hcau (ENNReal.ofReal (ε / (B + 1) / 2)) (ENNReal.ofReal_pos.mpr hpos)
    refine ⟨N, fun m hm n hn z _ => ?_⟩
    rw [dist_eq_norm]
    have h1 := norm_mol_diff_le hK hl (hg 1) (hg' 0) hg1L hhL m n z
    have h2 : (eLpNorm (fun w => mol m (g' 0) w - mol n (g' 0) w) 2 volume).toReal ≤
        ε / (B + 1) / 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hN m hm n hn)
      rwa [ENNReal.toReal_ofReal hpos.le] at this
    have h3 : B / (B + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have key : B * (ε / (B + 1) / 2) = (ε / 2) * (B / (B + 1)) := by ring
    calc ‖mol m v z - mol n v z‖ ≤ B * _ := h1
      _ ≤ B * (ε / (B + 1) / 2) := mul_le_mul_of_nonneg_left h2 hB0
      _ = (ε / 2) * (B / (B + 1)) := key
      _ ≤ ε / 2 := mul_le_of_le_one_right (by positivity) h3
      _ < ε := by linarith
  have hlimz : ∀ z, ∃ y, Tendsto (fun n => mol n v z) atTop (𝓝 y) := fun z =>
    cauchySeq_tendsto_of_complete (hunif.cauchySeq (mem_univ z))
  choose w hw using hlimz
  have hTU : TendstoUniformly (fun n => mol n v) w atTop :=
    tendstoUniformlyOn_univ.mp (hunif.tendstoUniformlyOn_of_tendsto fun z _ => hw z)
  have hwc : Continuous w :=
    hTU.continuous (Eventually.of_forall fun n => (mol_contDiff n hvl).continuous).frequently
  refine ⟨w, hwc, ?_, fun z hz => ?_⟩
  · have hm := tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) (tendsto_mol hl.1)
    obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
    filter_upwards [hae] with x hx
    exact tendsto_nhds_unique hx ((hw x).comp hns.tendsto_atTop)
  · have h0 : ∀ n, mol n v z = 0 := fun n =>
      image_eq_zero_of_notMem_tsupport fun h => hz (tsupport_mol_subset n hl.2 h)
    exact tendsto_nhds_unique (hw z) (by simp [h0])

end Base

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
