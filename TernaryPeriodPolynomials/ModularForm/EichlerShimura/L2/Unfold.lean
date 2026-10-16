module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Exact
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Overlap

@[expose] public section


/-!
# Unfolding the averaged exact forms

For `ψ` a smooth compactly supported field and `u` an equivariant vector, the inner product of the
weighted coordinates of `d (avg ψ)` with `u` equals the flat integral of `⟪coord (dψ), ϑ^{-1/2} u⟫`
(`inner_xvec_avg`).  This is the unfolding step: the sum over `Γ` is removed using the invariance
vectors of `eqvSub` and `∑_γ ϑ ∘ γ = 1`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one IsCover cutoff cutoff_nonneg)
open TernaryPeriodPolynomials.Argument.ESFoundations.Weyl (XP mkX)

variable {Γ : Subgroup SL(2, ℤ)} {d : ℕ}

namespace HodgeDatum

variable (D : HodgeDatum Γ d) (W : Weights Γ)

/-- The linear map sending a covector at `z` to its weighted `S`-coordinates. -/
def Tz (z : ℂ) : (ℂ →L[ℝ] Wd d) →L[ℝ] XP (Wd d) :=
  Real.sqrt (W.θ z) • (Weyl.inlX ∘L ((D.S z).restrictScalars ℝ) ∘L
      ContinuousLinearMap.apply ℝ (Wd d) (1 : ℂ) +
    Weyl.inrX ∘L ((D.S z).restrictScalars ℝ) ∘L ContinuousLinearMap.apply ℝ (Wd d) Complex.I)

theorem wcoord_eq (L : Form d) (z : ℂ) : D.wcoord W L z = D.Tz W z (L z) := by
  unfold wcoord coord Tz
  rw [Weyl.mkX_eq_add]
  rfl

end HodgeDatum

theorem cptForm_fderiv {ψ : ℂ → Wd d} (hψ : IsTestW ψ) : CptForm (fun w => fderiv ℝ ψ w) := by
  refine ⟨(hψ.1.continuous_fderiv (by simp)).continuousOn, tsupport ψ, hψ.2.1, hψ.2.2,
    fun z _ hz => fderiv_of_notMem_tsupport ℝ hz⟩

namespace HodgeDatum

variable (D : HodgeDatum Γ d) {W : Weights Γ}

theorem dterm_ne_zero {ψ : ℂ → Wd d} (γ : Γ) {z : ℂ} (hz : z ∈ U)
    (h : D.slash γ⁻¹ (fun w => fderiv ℝ ψ w) z ≠ 0) : mob (γ : SL(2, ℤ))⁻¹ z ∈ tsupport ψ := by
  by_contra hn
  apply h
  rw [slash_eq_comp D γ⁻¹ _ hz, Subgroup.coe_inv, fderiv_of_notMem_tsupport ℝ hn]
  ext v
  simp

theorem avg_approx (hR : IsCover Γ W.R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) : D.Approx (D.avg ψ) := by
  refine ⟨contDiffOn_avg hR hψ, eqvFun_avg hR hψ, tsupport ψ, hψ.2.1, hψ.2.2, fun z hz hfree => ?_⟩
  exact fderiv_avg_eq_zero hR hψ hz fun γ => hfree γ

theorem finite_support_dterm (hR : IsCover Γ W.R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) {z : ℂ}
    (hz : z ∈ U) : (Function.support fun γ : Γ => D.slash γ⁻¹ (fun w => fderiv ℝ ψ w) z).Finite := by
  obtain ⟨V, hV, T, hT⟩ := exists_local_finite hR hψ hz
  refine T.finite_toSet.subset fun γ hγ => hT z (mem_of_mem_nhds hV) γ ?_
  have := dterm_ne_zero D γ hz hγ
  simpa using this

theorem wcoord_avg (hR : IsCover Γ W.R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) {z : ℂ} (hz : z ∈ U) :
    D.wcoord W (fun w => fderiv ℝ (D.avg ψ) w) z =
      ∑ᶠ γ : Γ, D.wcoord W (D.slash γ⁻¹ (fun w => fderiv ℝ ψ w)) z := by
  rw [wcoord_eq, fderiv_avg hR hψ hz]
  simp_rw [wcoord_eq]
  exact map_finsum (D.Tz W z) (finite_support_dterm D hR hψ hz)

theorem mult_dterm (hR : IsCover Γ W.R) {ψ : ℂ → Wd d} (hψ : IsTestW ψ) :
    ∃ N : ℕ, ∀ z ∈ U, {γ : Γ | D.wcoord W (D.slash γ⁻¹ (fun w => fderiv ℝ ψ w)) z ≠ 0}.Finite ∧
      {γ : Γ | D.wcoord W (D.slash γ⁻¹ (fun w => fderiv ℝ ψ w)) z ≠ 0}.ncard ≤ N := by
  obtain ⟨N, hN⟩ := exists_mult_bound hR hψ.2.1 hψ.2.2
  refine ⟨N, fun z hz => ?_⟩
  obtain ⟨hfin, hcard⟩ := hN z
  have hsub : {γ : Γ | D.wcoord W (D.slash γ⁻¹ (fun w => fderiv ℝ ψ w)) z ≠ 0} ⊆
      {γ : Γ | mob (γ : SL(2, ℤ))⁻¹ z ∈ tsupport ψ} := by
    intro γ hγ
    refine dterm_ne_zero D γ hz fun h0 => hγ ?_
    simp [wcoord, coord, h0]
    right
    rfl
  exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans hcard⟩

theorem edens_slash (γ : Γ) (L : Form d) {z : ℂ} (hz : z ∈ U) :
    D.edens (D.slash γ L) z = jac (γ : SL(2, ℤ)) z * D.edens L (mob (γ : SL(2, ℤ)) z) := by
  rw [← pairE_self, D.pairE_slash γ L L hz, pairE_self]
  rfl

theorem lintegral_edens_lt_top {L : Form d} (hL : CptForm L) :
    ∫⁻ z in U, ENNReal.ofReal (D.edens L z) < ⊤ := by
  obtain ⟨hc, K, hK, hKU, h0⟩ := hL
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn ((Weights.continuousOn_edens D hc).mono hKU)
  have hsupp : ∀ z ∈ U, ENNReal.ofReal (D.edens L z) ≤ K.indicator (fun _ => ENNReal.ofReal M) z := by
    intro z hz
    by_cases hzK : z ∈ K
    · rw [Set.indicator_of_mem hzK]
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM z hzK))
    · rw [Set.indicator_of_notMem hzK]
      simp [HodgeDatum.edens, h0 z hz hzK]
  calc ∫⁻ z in U, ENNReal.ofReal (D.edens L z)
      ≤ ∫⁻ z in U, K.indicator (fun _ => ENNReal.ofReal M) z :=
        setLIntegral_mono' isOpen_U.measurableSet hsupp
    _ ≤ ∫⁻ z, K.indicator (fun _ => ENNReal.ofReal M) z := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal M * volume K := by rw [lintegral_indicator_const hK.isClosed.measurableSet]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

theorem lintegral_dterm (γ : Γ) {L : Form d} (hL : ContinuousOn L U) :
    ∫⁻ z in U, ENNReal.ofReal (‖D.wcoord W (D.slash γ⁻¹ L) z‖ ^ 2) =
      ∫⁻ z in U, ENNReal.ofReal (W.θ (mob (γ : SL(2, ℤ)) z)) * ENNReal.ofReal (D.edens L z) := by
  set g : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (W.θ (mob (γ : SL(2, ℤ)) w)) *
    ENNReal.ofReal (D.edens L w) with hg
  have hgm : AEMeasurable g (volume.restrict U) :=
    (Weights.aemeasurable_ofReal_of_continuousOn (W.continuousOn_θ.comp
      (Partition.contDiffOn_mob (γ : SL(2, ℤ)) (n := 0)).continuousOn (Partition.mapsTo_mob _))).mul
      (Weights.aemeasurable_ofReal_of_continuousOn (Weights.continuousOn_edens D hL))
  rw [← lintegral_flat_mob ((γ : SL(2, ℤ))⁻¹) hgm]
  refine setLIntegral_congr_fun isOpen_U.measurableSet fun z hz => ?_
  have e3 : mob (γ : SL(2, ℤ)) (mob ((γ : SL(2, ℤ))⁻¹) z) = z := by
    rw [← mob_mul, mul_inv_cancel, mob_one hz]
  have e := D.edens_slash γ⁻¹ L hz
  rw [D.norm_wcoord_sq W, e, Subgroup.coe_inv, hg]
  simp only [e3]
  rw [ENNReal.ofReal_mul (W.θ_nonneg z), ENNReal.ofReal_mul (jac_nonneg _ _)]
  ring

theorem tsum_lintegral_dterm_lt_top {ψ : ℂ → Wd d} (hψ : IsTestW ψ) :
    ∑' γ : Γ, ∫⁻ z in U, ENNReal.ofReal
      (‖D.wcoord W (D.slash γ⁻¹ (fun w => fderiv ℝ ψ w)) z‖ ^ 2) < ⊤ := by
  have hc := (cptForm_fderiv hψ).1
  have h1 : ∀ γ : Γ, ∫⁻ z in U, ENNReal.ofReal
      (‖D.wcoord W (D.slash γ⁻¹ (fun w => fderiv ℝ ψ w)) z‖ ^ 2) =
      ∫⁻ z in U, ENNReal.ofReal (W.θ (mob (γ : SL(2, ℤ)) z)) *
        ENNReal.ofReal (D.edens (fun w => fderiv ℝ ψ w) z) := fun γ => lintegral_dterm D γ hc
  simp_rw [h1]
  have hm : ∀ γ : Γ, AEMeasurable (fun z => ENNReal.ofReal (W.θ (mob (γ : SL(2, ℤ)) z)) *
        ENNReal.ofReal (D.edens (fun w => fderiv ℝ ψ w) z)) (volume.restrict U) := fun γ =>
    (Weights.aemeasurable_ofReal_of_continuousOn (W.continuousOn_θ.comp
      (Partition.contDiffOn_mob (γ : SL(2, ℤ)) (n := 0)).continuousOn
      (Partition.mapsTo_mob _))).mul
      (Weights.aemeasurable_ofReal_of_continuousOn (Weights.continuousOn_edens D hc))
  rw [← lintegral_tsum hm]
  have h2 : ∫⁻ z in U, ∑' γ : Γ, ENNReal.ofReal (W.θ (mob (γ : SL(2, ℤ)) z)) *
        ENNReal.ofReal (D.edens (fun w => fderiv ℝ ψ w) z) =
      ∫⁻ z in U, ENNReal.ofReal (D.edens (fun w => fderiv ℝ ψ w) z) := by
    refine setLIntegral_congr_fun isOpen_U.measurableSet fun z hz => ?_
    rw [ENNReal.tsum_mul_right, show (∑' γ : Γ, ENNReal.ofReal (W.θ (mob (γ : SL(2, ℤ)) z))) = 1 from
      ennreal_tsum_theta_comp W.hR W.ha W.hs hz, one_mul]
  rw [h2]
  exact lintegral_edens_lt_top D (cptForm_fderiv hψ)

/-- The vector `ϑ^{-1/2} coord L` as a function. -/
def ucoord (W : Weights Γ) (L : Form d) (z : ℂ) : XP (Wd d) := (Real.sqrt (W.θ z))⁻¹ • D.coord L z

theorem memLp_ucoord {L : Form d} (hL : CptForm L) : MemLp (D.ucoord W L) 2 (volume.restrict U) := by
  obtain ⟨hc, K, hK, hKU, h0⟩ := hL
  have hcont : ContinuousOn (D.ucoord W L) U :=
    (W.continuousOn_θ.sqrt.inv₀ fun z hz => (Real.sqrt_pos.mpr (W.θ_pos hz)).ne').smul
      (D.continuousOn_coord hc)
  refine memLp_of_cpt hcont hK hKU fun z hz hzK => ?_
  have e0 : mkX (0 : Wd d) 0 = 0 := rfl
  simp [ucoord, coord, h0 z hz hzK, e0]

theorem inner_xvec_avg {ψ : ℂ → Wd d} (hψ : IsTestW ψ) {u : Hs d} (hu : u ∈ D.eqvSub W) :
    ⟪D.xvec W (Approx.good D W (avg_approx D W.hR hψ)), u⟫_ℝ =
      ∫ z in U, ⟪D.ucoord W (fun w => fderiv ℝ ψ w) z, (u : ℂ → XP (Wd d)) z⟫_ℝ := by
  set L₁ : Form d := fun w => fderiv ℝ ψ w with hL₁def
  have hL₁ : CptForm L₁ := cptForm_fderiv hψ
  set A : Γ → ℂ → XP (Wd d) := fun γ => D.wcoord W (D.slash γ⁻¹ L₁) with hA
  have hAmem : ∀ γ : Γ, MemLp (A γ) 2 (volume.restrict U) := fun γ =>
    CptForm.memLp D W (CptForm.slash D γ⁻¹ hL₁)
  have huf : AEStronglyMeasurable (u : ℂ → XP (Wd d)) (volume.restrict U) :=
    (Lp.stronglyMeasurable u).aestronglyMeasurable
  have hu2 : ∫⁻ z, ENNReal.ofReal (‖(u : ℂ → XP (Wd d)) z‖ ^ 2) ∂(volume.restrict U) < ⊤ :=
    ((memLp_two_iff_integrable_sq_norm huf).mp (Lp.memLp u)).lintegral_lt_top
  obtain ⟨N, hN⟩ := mult_dterm D (W := W) W.hR hψ
  have hUae : ∀ᵐ z ∂(volume.restrict U), z ∈ U := ae_restrict_mem isOpen_U.measurableSet
  have hNae : ∀ᵐ z ∂(volume.restrict U),
      {γ : Γ | A γ z ≠ 0}.Finite ∧ {γ : Γ | A γ z ≠ 0}.ncard ≤ N := by
    filter_upwards [hUae] with z hz
    exact hN z hz
  have hx : ∀ᵐ z ∂(volume.restrict U),
      D.wcoord W (fun w => fderiv ℝ (D.avg ψ) w) z = ∑ᶠ γ : Γ, A γ z := by
    filter_upwards [hUae] with z hz
    exact wcoord_avg D W.hR hψ hz
  obtain ⟨-, -, hsum⟩ := integral_tsum_inner (μ := volume.restrict U) (A := A)
    (u := (u : ℂ → XP (Wd d))) (x := D.wcoord W (fun w => fderiv ℝ (D.avg ψ) w))
    (fun γ => (hAmem γ).aestronglyMeasurable) huf (tsum_lintegral_dterm_lt_top D hψ) hu2 hNae hx
  -- the left side
  have hlhs : ⟪D.xvec W (Approx.good D W (avg_approx D W.hR hψ)), u⟫_ℝ =
      ∫ z in U, ⟪D.wcoord W (fun w => fderiv ℝ (D.avg ψ) w) z, (u : ℂ → XP (Wd d)) z⟫_ℝ := by
    unfold xvec
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(Good.memLp D W (Approx.good D W (avg_approx D W.hR hψ))).coeFn_toLp] with z hz
    rw [hz]
  -- the terms
  set h : ℂ → ℝ := fun z => ⟪D.ucoord W L₁ z, (u : ℂ → XP (Wd d)) z⟫_ℝ with hh
  have hhint : Integrable h (volume.restrict U) := by
    have := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) ((memLp_ucoord D (W := W) hL₁).toLp _) u
    refine this.congr ?_
    filter_upwards [(memLp_ucoord D (W := W) hL₁).coeFn_toLp] with z hz
    rw [hz]
  have hterm : ∀ γ : Γ, ∫ z in U, ⟪A γ z, (u : ℂ → XP (Wd d)) z⟫_ℝ =
      ∫ z in U, W.θ (mob (γ : SL(2, ℤ)) z) * h z := by
    intro γ
    have h0 := (mem_eqvSub_iff D W).mp hu γ L₁ hL₁
    unfold mvec at h0
    rw [inner_sub_left, sub_eq_zero] at h0
    have e1 : ⟪(hAmem γ).toLp (A γ), u⟫_ℝ = ∫ z in U, ⟪A γ z, (u : ℂ → XP (Wd d)) z⟫_ℝ := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [(hAmem γ).coeFn_toLp] with z hz
      rw [hz]
    have e2 : ⟪(D.memLp_tcoord W γ hL₁).toLp (D.tcoord W γ L₁), u⟫_ℝ =
        ∫ z in U, W.θ (mob (γ : SL(2, ℤ)) z) * h z := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [(D.memLp_tcoord W γ hL₁).coeFn_toLp] with z hz
      rw [hz]
      simp only [tcoord, ucoord, hh, div_eq_mul_inv, mul_smul, real_inner_smul_left]
    rw [← e1, ← e2]
    exact h0
  have hlim : HasSum (fun γ : Γ => ∫ z in U, W.θ (mob (γ : SL(2, ℤ)) z) * h z)
      (∫ z in U, h z) := by
    refine hasSum_integral_of_dominated_convergence (μ := volume.restrict U)
      (fun (γ : Γ) (z : ℂ) => W.θ (mob (γ : SL(2, ℤ)) z) * |h z|) ?_ ?_ ?_ ?_ ?_
    · intro γ
      exact ((W.continuousOn_θ.comp (Partition.contDiffOn_mob (γ : SL(2, ℤ)) (n := 0)).continuousOn
        (Partition.mapsTo_mob _)).aestronglyMeasurable isOpen_U.measurableSet).mul hhint.1
    · intro γ
      refine Eventually.of_forall fun z => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (W.θ_nonneg _), Real.norm_eq_abs]
    · filter_upwards [hUae] with z hz
      exact ((W.tsum_θ_comp hz).mul_right |h z|).summable
    · refine hhint.norm.congr ?_
      filter_upwards [hUae] with z hz
      rw [((W.tsum_θ_comp hz).mul_right |h z|).tsum_eq, one_mul, Real.norm_eq_abs]
    · filter_upwards [hUae] with z hz
      simpa using (W.tsum_θ_comp hz).mul_right (h z)
  simp_rw [hterm] at hsum
  rw [hlhs, hsum.unique hlim]


end HodgeDatum

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
