module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Harmonic

@[expose] public section


/-!
# The smooth representative of a harmonic vector

A harmonic vector `u` is represented by a smooth form `L₀ = formOf a' b'` (Weyl's lemma applied to
the coefficients `S⁻¹ (ϑ^{-1/2} u)`), which has finite energy.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one IsCover cutoff cutoff_nonneg)
open TernaryPeriodPolynomials.Argument.ESFoundations.Weyl (XP mkX dir IsTest)

variable {Γ : Subgroup SL(2, ℤ)} {d : ℕ}

/-- The real-linear form with values `a` on `1` and `b` on `i`. -/
def formOf (a b : ℂ → Wd d) : Form d := fun z =>
  ContinuousLinearMap.smulRightL ℝ ℂ (Wd d) Complex.reCLM (a z) +
    ContinuousLinearMap.smulRightL ℝ ℂ (Wd d) Complex.imCLM (b z)

theorem formOf_apply (a b : ℂ → Wd d) (z v : ℂ) : formOf a b z v = v.re • a z + v.im • b z := by
  simp [formOf]

theorem formOf_one (a b : ℂ → Wd d) (z : ℂ) : formOf a b z 1 = a z := by simp [formOf_apply]

theorem formOf_I (a b : ℂ → Wd d) (z : ℂ) : formOf a b z Complex.I = b z := by
  simp [formOf_apply]

theorem contDiffOn_formOf {a b : ℂ → Wd d} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (formOf a b) U :=
  (contDiffOn_const.clm_apply ha).add (contDiffOn_const.clm_apply hb)

theorem fderiv_eq_formOf (φ : ℂ → Wd d) (z : ℂ) :
    fderiv ℝ φ z = formOf (fun w => fderiv ℝ φ w (dir 0)) (fun w => fderiv ℝ φ w (dir 1)) z := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [formOf_apply]
  have h : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  calc fderiv ℝ φ z v = fderiv ℝ φ z ((v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I) := by
        rw [← h]
    _ = _ := by
        rw [(fderiv ℝ φ z).map_add, (fderiv ℝ φ z).map_smul, (fderiv ℝ φ z).map_smul]
        simp [dir]

theorem HodgeDatum.coord_formOf (D : HodgeDatum Γ d) (a b : ℂ → Wd d) (z : ℂ) :
    D.coord (formOf a b) z = mkX (D.S z (a z)) (D.S z (b z)) := by
  simp [HodgeDatum.coord, formOf_one, formOf_I]

namespace HodgeDatum

variable (D : HodgeDatum Γ d) (W : Weights Γ)

/-- **Weyl regularity for harmonic vectors.** -/
theorem exists_smooth {u : Hs d} (hu : Harmonic D W u) :
    ∃ a' b' : ℂ → Wd d, ContDiffOn ℝ ∞ a' U ∧ ContDiffOn ℝ ∞ b' U ∧
      (D.acoef W u =ᵐ[volume.restrict U] a') ∧ (D.bcoef W u =ᵐ[volume.restrict U] b') ∧
      (∀ z ∈ U, fderiv ℝ b' z (dir 0) = fderiv ℝ a' z (dir 1)) ∧
      (∀ z ∈ U, fderiv ℝ (fun z => D.H z (a' z)) z (dir 0) +
        fderiv ℝ (fun z => D.H z (b' z)) z (dir 1) = 0) :=
  Weyl.weyl_closed_coclosed_strong D.hField (fun _ hK hKU => D.memLp_acoef W u hK hKU)
    (fun _ hK hKU => D.memLp_bcoef W u hK hKU)
    (fun _ hψ hψU => D.closed_weak W hu hψ hψU)
    (fun _ hφ hc hU => D.coclosed_weak W hu hφ hc hU)

theorem wcoord_formOf_ae {u : Hs d} {a' b' : ℂ → Wd d} (ha : D.acoef W u =ᵐ[volume.restrict U] a')
    (hb : D.bcoef W u =ᵐ[volume.restrict U] b') :
    (u : ℂ → XP (Wd d)) =ᵐ[volume.restrict U] D.wcoord W (formOf a' b') := by
  filter_upwards [ha, hb, ae_restrict_mem isOpen_U.measurableSet] with z h1 h2 hz
  have h : 0 < Real.sqrt (W.θ z) := Real.sqrt_pos.mpr (W.θ_pos hz)
  unfold wcoord
  rw [coord_formOf, ← h1, ← h2, ← ucoef_eq D W u hz]
  unfold ucoef
  rw [smul_smul, mul_inv_cancel₀ h.ne', one_smul]

theorem good_of_ae {u : Hs d} {L : Form d} (hL : ContinuousOn L U)
    (h : (u : ℂ → XP (Wd d)) =ᵐ[volume.restrict U] D.wcoord W L) : Good D W L := by
  refine ⟨hL, ?_⟩
  have huf : AEStronglyMeasurable (u : ℂ → XP (Wd d)) (volume.restrict U) :=
    (Lp.stronglyMeasurable u).aestronglyMeasurable
  have h2 : ∫⁻ z, ENNReal.ofReal (‖(u : ℂ → XP (Wd d)) z‖ ^ 2) ∂(volume.restrict U) < ⊤ :=
    ((memLp_two_iff_integrable_sq_norm huf).mp (Lp.memLp u)).lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr_ae ?_
  filter_upwards [h] with z hz
  rw [hz, D.norm_wcoord_sq W, ENNReal.ofReal_mul (W.θ_nonneg z)]

theorem integral_cov' (γ : Γ) {L₁ L : Form d} (h₁ : ContinuousOn L₁ U) (hL : ContinuousOn L U) :
    ∫ z in U, W.θ z * D.pairE (D.slash γ⁻¹ L₁) L z =
      ∫ z in U, W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ (D.slash γ L) z := by
  set g : ℂ → ℝ := fun w => W.θ (mob (γ : SL(2, ℤ)) w) * D.pairE L₁ (D.slash γ L) w with hg
  have hgc : ContinuousOn g U :=
    (W.continuousOn_θ.comp (Partition.contDiffOn_mob (γ : SL(2, ℤ)) (n := 0)).continuousOn
      (Partition.mapsTo_mob _)).mul (D.continuousOn_pairE h₁ (continuousOn_slash D γ hL))
  have h := integral_flat_mob ((γ : SL(2, ℤ))⁻¹) (hgc.aestronglyMeasurable isOpen_U.measurableSet)
  rw [← h]
  refine setIntegral_congr_fun isOpen_U.measurableSet fun w hw => ?_
  have e1 : D.pairE (D.slash γ⁻¹ L₁) L w =
      D.pairE (D.slash γ⁻¹ L₁) (D.slash γ⁻¹ (D.slash γ L)) w := by
    unfold HodgeDatum.pairE
    have := slash_slash_inv D γ⁻¹ L hw
    rw [inv_inv] at this
    rw [this]
  have e2 := D.pairE_slash γ⁻¹ L₁ (D.slash γ L) hw
  have e3 : mob (γ : SL(2, ℤ)) (mob ((γ : SL(2, ℤ))⁻¹) w) = w := by
    rw [← mob_mul, mul_inv_cancel, mob_one hw]
  simp only [Subgroup.coe_inv] at e2
  simp only [hg, e3, jac, smul_eq_mul]
  rw [e1, e2]
  ring

theorem inner_mvec_ae (γ : Γ) {L₁ : Form d} (hL₁ : CptForm L₁) {u : Hs d} {L : Form d}
    (h : (u : ℂ → XP (Wd d)) =ᵐ[volume.restrict U] D.wcoord W L) :
    ⟪D.mvec W γ hL₁, u⟫_ℝ = (∫ z in U, W.θ z * D.pairE (D.slash γ⁻¹ L₁) L z) -
      ∫ z in U, W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ L z := by
  have hA := CptForm.memLp D W (CptForm.slash D γ⁻¹ hL₁)
  have hT := D.memLp_tcoord W γ hL₁
  have e1 : ⟪hA.toLp (D.wcoord W (D.slash γ⁻¹ L₁)), u⟫_ℝ =
      ∫ z in U, W.θ z * D.pairE (D.slash γ⁻¹ L₁) L z := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hA.coeFn_toLp, h] with z h1 h2
    rw [h1, h2, D.inner_wcoord W]
  have e2 : ⟪hT.toLp (D.tcoord W γ L₁), u⟫_ℝ =
      ∫ z in U, W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ L z := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hT.coeFn_toLp, h, ae_restrict_mem isOpen_U.measurableSet] with z h1 h2 hz
    rw [h1, h2, D.inner_tcoord W γ L₁ L hz]
  unfold mvec
  rw [inner_sub_left, e1, e2]

theorem integrableOn_of_cpt {F : ℂ → ℝ} (hF : ContinuousOn F U) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) (h0 : ∀ z ∈ U, z ∉ K → F z = 0) : Integrable F (volume.restrict U) := by
  have hres : (volume.restrict U).restrict K = volume.restrict K := by
    rw [Measure.restrict_restrict hK.measurableSet, inter_eq_left.mpr hKU]
  have h1 : IntegrableOn F K (volume.restrict U) := by
    unfold IntegrableOn
    rw [hres]
    exact (hF.mono hKU).integrableOn_compact hK
  have h2 : Integrable (K.indicator F) (volume.restrict U) :=
    (integrable_indicator_iff hK.measurableSet).mpr h1
  refine h2.congr ?_
  filter_upwards [ae_restrict_mem isOpen_U.measurableSet] with z hz
  by_cases hzK : z ∈ K
  · simp [hzK]
  · simp [hzK, h0 z hz hzK]

theorem clm_ext_one_I {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (T : ℂ →L[ℝ] X)
    (h1 : T 1 = 0) (hI : T Complex.I = 0) : T = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  rw [h, T.map_add, T.map_smul, T.map_smul, h1, hI]
  simp

theorem eqv_of_mem_eqvSub {u : Hs d} {L : Form d} (hL : ContinuousOn L U)
    (h : (u : ℂ → XP (Wd d)) =ᵐ[volume.restrict U] D.wcoord W L) (hu : u ∈ D.eqvSub W) :
    D.Eqv L := by
  intro γ w hw
  set Δ : Form d := fun z => D.slash γ L z - L z with hΔ
  have hΔc : ContinuousOn Δ U := (continuousOn_slash D γ hL).sub hL
  set f : ℂ → ℝ := fun z => W.θ (mob (γ : SL(2, ℤ)) z) * D.edens Δ z with hf
  have hfc : ContinuousOn f U :=
    (W.continuousOn_θ.comp (Partition.contDiffOn_mob (γ : SL(2, ℤ)) (n := 0)).continuousOn
      (Partition.mapsTo_mob _)).mul (Weights.continuousOn_edens D hΔc)
  have key : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ z, g z • f z = 0 := by
    intro g hg hgc hgU
    set L₁ : Form d := fun z => g z • Δ z with hL₁def
    have hL₁c : ContinuousOn L₁ U := hg.continuous.continuousOn.smul hΔc
    have hL₁ : CptForm L₁ := by
      refine ⟨hL₁c, tsupport g, hgc, hgU, fun z _ hz => ?_⟩
      show g z • Δ z = 0
      rw [image_eq_zero_of_notMem_tsupport hz]
      ext v
      simp
    have h0 := (mem_eqvSub_iff D W).mp hu γ L₁ hL₁
    rw [D.inner_mvec_ae W γ hL₁ h, D.integral_cov' W γ hL₁c hL, sub_eq_zero] at h0
    have hcont : ∀ L' : Form d, ContinuousOn L' U → ContinuousOn
        (fun z => W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ L' z) U := fun L' hL' =>
      (W.continuousOn_θ.comp (Partition.contDiffOn_mob (γ : SL(2, ℤ)) (n := 0)).continuousOn
        (Partition.mapsTo_mob _)).mul (D.continuousOn_pairE hL₁c hL')
    have hvan : ∀ L' : Form d, ∀ z ∈ U, z ∉ tsupport g →
        W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ L' z = 0 := by
      intro L' z _ hz
      simp [HodgeDatum.pairE, hL₁def, image_eq_zero_of_notMem_tsupport hz]
    have i1 := integrableOn_of_cpt (hcont _ (continuousOn_slash D γ hL)) hgc hgU (hvan _)
    have i2 := integrableOn_of_cpt (hcont _ hL) hgc hgU (hvan _)
    have h3 : ∫ z in U, (W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ (D.slash γ L) z -
        W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ L z) = 0 := by
      rw [integral_sub i1 i2, h0, sub_self]
    have h4 : ∀ z ∈ U, W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ (D.slash γ L) z -
        W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ L z = g z • f z := by
      intro z hz
      have e1 : ∀ v, L₁ z v = g z • (D.slash γ L z v - L z v) := fun v => rfl
      have e2 : ∀ v, Δ z v = D.slash γ L z v - L z v := fun v => rfl
      have hS : ∀ (r : ℝ) (x : Wd d), D.S z (r • x) = r • D.S z x := fun r x => by simp
      simp only [hf, HodgeDatum.pairE, HodgeDatum.edens, e1, e2, hS, map_sub,
        ← real_inner_self_eq_norm_sq, real_inner_smul_left, inner_sub_left, inner_sub_right]
      ring
    rw [setIntegral_congr_fun isOpen_U.measurableSet h4] at h3
    rw [← h3]
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    have : g z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hgU h')
    simp [this]
  have hae : ∀ᵐ z, z ∈ U → f z = 0 :=
    isOpen_U.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hfc.locallyIntegrableOn isOpen_U.measurableSet) key
  have hf0 : f =ᵐ[volume.restrict U] 0 := by
    rw [EventuallyEq, ae_restrict_iff' isOpen_U.measurableSet]
    filter_upwards [hae] with z hz hzU using hz hzU
  have hfw := Measure.eqOn_open_of_ae_eq hf0 isOpen_U hfc continuousOn_const hw
  have hθ := W.θ_pos (Partition.mob_mem (γ : SL(2, ℤ)) w)
  have hed : D.edens Δ w = 0 := by
    simp only [hf, Pi.zero_apply] at hfw
    exact (mul_eq_zero.mp hfw).resolve_left hθ.ne'
  have hS : ∀ x : Wd d, D.S w x = 0 → x = 0 := by
    intro x hx
    have := Ring.inverse_mul_cancel (D.S w) (D.S_unit w hw)
    have h2 := congrArg (fun T : Wd d →L[ℂ] Wd d => T x) this
    simpa [hx] using h2.symm
  have h1 : Δ w 1 = 0 := by
    apply hS
    have : ‖D.S w (Δ w 1)‖ ^ 2 = 0 := by
      have := D.edens_nonneg Δ w
      unfold HodgeDatum.edens at hed this
      nlinarith [sq_nonneg ‖D.S w (Δ w Complex.I)‖, sq_nonneg ‖D.S w (Δ w 1)‖]
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)
  have hI : Δ w Complex.I = 0 := by
    apply hS
    have : ‖D.S w (Δ w Complex.I)‖ ^ 2 = 0 := by
      unfold HodgeDatum.edens at hed
      nlinarith [sq_nonneg ‖D.S w (Δ w Complex.I)‖, sq_nonneg ‖D.S w (Δ w 1)‖]
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)
  have := clm_ext_one_I (Δ w) h1 hI
  simp only [hΔ] at this
  exact sub_eq_zero.mp this

end HodgeDatum

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
