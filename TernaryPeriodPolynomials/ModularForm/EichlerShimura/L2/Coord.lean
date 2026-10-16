module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Weights
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.System

@[expose] public section


/-!
# Continuity and support of slashed forms

Compactly supported continuous forms are preserved by the slash action (`CptForm.slash`),
`slash` is an action (`slash_slash_inv`), and the `S`-coordinates of a form
(`coord`) realise the pairing `pairE` as an inner product in `XP (ℂ^d)`.

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

theorem continuousOn_mobDeriv (γ : SL(2, ℤ)) : ContinuousOn (mobDeriv γ) U := by
  unfold mobDeriv
  refine continuousOn_const.div (by unfold jfun; fun_prop) fun z hz => ?_
  exact pow_ne_zero 2 (Partition.denom_ne_zero' γ hz)

/-- The slash action in terms of the multiplication by `mobDeriv`. -/
theorem slash_eq_comp (D : HodgeDatum Γ d) (γ : Γ) (L : Form d) {w : ℂ} (hw : w ∈ U) :
    D.slash γ L w = (D.ρR γ⁻¹).comp ((L (mob (γ : SL(2, ℤ)) w)).comp
      (ContinuousLinearMap.mul ℝ ℂ (mobDeriv (γ : SL(2, ℤ)) w))) := by
  ext v
  simp [HodgeDatum.slash, fderiv_mob_apply _ hw]

theorem continuousOn_slash (D : HodgeDatum Γ d) (γ : Γ) {L : Form d} (hL : ContinuousOn L U) :
    ContinuousOn (D.slash γ L) U := by
  have h1 : ContinuousOn (fun w => L (mob (γ : SL(2, ℤ)) w)) U :=
    hL.comp (Partition.contDiffOn_mob (γ : SL(2, ℤ)) (n := 0)).continuousOn (Partition.mapsTo_mob _)
  have h2 : ContinuousOn (fun w => ContinuousLinearMap.mul ℝ ℂ (mobDeriv (γ : SL(2, ℤ)) w)) U :=
    (ContinuousLinearMap.mul ℝ ℂ).continuous.comp_continuousOn (continuousOn_mobDeriv _)
  have h3 : ContinuousOn (fun w => (D.ρR γ⁻¹).comp ((L (mob (γ : SL(2, ℤ)) w)).comp
      (ContinuousLinearMap.mul ℝ ℂ (mobDeriv (γ : SL(2, ℤ)) w)))) U :=
    continuousOn_const.clm_comp (h1.clm_comp h2)
  exact h3.congr fun w hw => slash_eq_comp D γ L hw

/-- Continuous forms vanishing outside a compact subset of `U`. -/
def CptForm (L : Form d) : Prop :=
  ContinuousOn L U ∧ ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ ∀ z ∈ U, z ∉ K → L z = 0

theorem CptForm.slash (D : HodgeDatum Γ d) (γ : Γ) {L : Form d} (hL : CptForm L) :
    CptForm (D.slash γ L) := by
  obtain ⟨hc, K, hK, hKU, h0⟩ := hL
  refine ⟨continuousOn_slash D γ hc, (fun k => mob ((γ : SL(2, ℤ))⁻¹) k) '' K,
    hK.image_of_continuousOn
      ((Partition.contDiffOn_mob ((γ : SL(2, ℤ))⁻¹) (n := 0)).continuousOn.mono hKU),
    ?_, fun z hz hzK => ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact Partition.mob_mem _ _
  · rw [slash_eq_comp D γ L hz]
    have : L (mob (γ : SL(2, ℤ)) z) = 0 := by
      refine h0 _ (Partition.mob_mem _ _) fun hk => hzK ⟨_, hk, ?_⟩
      show mob ((γ : SL(2, ℤ))⁻¹) (mob (γ : SL(2, ℤ)) z) = z
      rw [← mob_mul, inv_mul_cancel, mob_one hz]
    rw [this]
    ext v
    simp

theorem mobDeriv_inv_mul (γ : SL(2, ℤ)) {w : ℂ} (hw : w ∈ U) :
    mobDeriv γ⁻¹ (mob γ w) * mobDeriv γ w = 1 := by
  have h1 := Height.hasDerivAt_mob γ hw
  have h2 := Height.hasDerivAt_mob γ⁻¹ (Partition.mob_mem γ w)
  have h3 := h2.comp w h1
  have h4 : (mob γ⁻¹ ∘ mob γ) =ᶠ[𝓝 w] id := by
    filter_upwards [isOpen_U.mem_nhds hw] with z hz
    simp only [Function.comp_apply, id]
    rw [← mob_mul, inv_mul_cancel, mob_one hz]
  have h5 := h3.congr_of_eventuallyEq h4.symm
  exact ((hasDerivAt_id w).unique h5).symm

theorem slash_slash_inv (D : HodgeDatum Γ d) (γ : Γ) (L : Form d) {w : ℂ} (hw : w ∈ U) :
    D.slash γ (D.slash γ⁻¹ L) w = L w := by
  have hg : mob (γ : SL(2, ℤ)) w ∈ U := Partition.mob_mem _ _
  rw [slash_eq_comp D γ _ hw, slash_eq_comp D γ⁻¹ L hg]
  have e : mob (((γ⁻¹ : Γ) : SL(2, ℤ))) (mob (γ : SL(2, ℤ)) w) = w := by
    rw [← mob_mul, Subgroup.coe_inv, inv_mul_cancel, mob_one hw]
  rw [e]
  have hm : mobDeriv (((γ⁻¹ : Γ) : SL(2, ℤ))) (mob (γ : SL(2, ℤ)) w) * mobDeriv (γ : SL(2, ℤ)) w = 1 := by
    rw [Subgroup.coe_inv]; exact mobDeriv_inv_mul _ hw
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply']
  have hr : ∀ x : Wd d, D.ρR γ⁻¹ (D.ρR (γ⁻¹)⁻¹ x) = x := by
    intro x
    simp only [inv_inv]
    have h2 := congrArg (fun T : Wd d →L[ℂ] Wd d => T x) (D.ρ.map_mul γ⁻¹ γ)
    simp only [inv_mul_cancel, map_one] at h2
    exact h2.symm
  rw [hr, ← mul_assoc, hm, one_mul]

/-- The `S`-coordinates of a form, an element of `ℂ^d × ℂ^d`. -/
def HodgeDatum.coord (D : HodgeDatum Γ d) (L : Form d) (z : ℂ) : XP (Wd d) :=
  mkX (D.S z (L z 1)) (D.S z (L z Complex.I))

theorem HodgeDatum.inner_coord (D : HodgeDatum Γ d) (L₁ L₂ : Form d) (z : ℂ) :
    ⟪D.coord L₁ z, D.coord L₂ z⟫_ℝ = D.pairE L₁ L₂ z := by
  simp [HodgeDatum.coord, HodgeDatum.pairE]

theorem HodgeDatum.norm_coord_sq (D : HodgeDatum Γ d) (L : Form d) (z : ℂ) :
    ‖D.coord L z‖ ^ 2 = D.edens L z := by
  rw [← real_inner_self_eq_norm_sq, D.inner_coord, D.pairE_self]

theorem memLp_of_cpt {X : Type*} [NormedAddCommGroup X] {f : ℂ → X} (hf : ContinuousOn f U)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) (h0 : ∀ z ∈ U, z ∉ K → f z = 0) :
    MemLp f 2 (volume.restrict U) := by
  have hres : (volume.restrict U).restrict K = volume.restrict K := by
    rw [Measure.restrict_restrict hK.measurableSet, inter_eq_left.mpr hKU]
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have h1 : MemLp f 2 (volume.restrict K) := by
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hf.mono hKU)
    exact MemLp.of_bound ((hf.mono hKU).aestronglyMeasurable hK.measurableSet) M
      (ae_restrict_of_forall_mem hK.measurableSet hM)
  have h2 : MemLp (K.indicator f) 2 (volume.restrict U) :=
    (memLp_indicator_iff_restrict hK.measurableSet).mpr (by rw [hres]; exact h1)
  refine h2.ae_eq ?_
  filter_upwards [ae_restrict_mem isOpen_U.measurableSet] with z hz
  by_cases hzK : z ∈ K
  · simp [hzK]
  · simp [hzK, h0 z hz hzK]

theorem HodgeDatum.continuousOn_coord (D : HodgeDatum Γ d) {L : Form d} (hL : ContinuousOn L U) :
    ContinuousOn (D.coord L) U := by
  have h1 : ContinuousOn (fun z => D.S z (L z 1)) U :=
    D.S_smooth.continuousOn.clm_apply (hL.clm_apply continuousOn_const)
  have h2 : ContinuousOn (fun z => D.S z (L z Complex.I)) U :=
    D.S_smooth.continuousOn.clm_apply (hL.clm_apply continuousOn_const)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (Wd d) (Wd d)).symm.continuous.comp_continuousOn
    (h1.prodMk h2)

/-- The weighted `S`-coordinates `√ϑ · coord L`, the representative in the Hilbert space. -/
def HodgeDatum.wcoord (D : HodgeDatum Γ d) (W : Weights Γ) (L : Form d) (z : ℂ) : XP (Wd d) :=
  Real.sqrt (W.θ z) • D.coord L z

theorem HodgeDatum.continuousOn_wcoord (D : HodgeDatum Γ d) (W : Weights Γ) {L : Form d}
    (hL : ContinuousOn L U) : ContinuousOn (D.wcoord W L) U :=
  (W.continuousOn_θ.sqrt).smul (D.continuousOn_coord hL)

theorem HodgeDatum.norm_wcoord_sq (D : HodgeDatum Γ d) (W : Weights Γ) (L : Form d) (z : ℂ) :
    ‖D.wcoord W L z‖ ^ 2 = W.θ z * D.edens L z := by
  unfold HodgeDatum.wcoord
  rw [norm_smul, mul_pow, D.norm_coord_sq, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (W.θ_nonneg z)]

/-- A continuous form of finite weighted energy. -/
structure Good (D : HodgeDatum Γ d) (W : Weights Γ) (L : Form d) : Prop where
  cont : ContinuousOn L U
  fin : ∫⁻ z in U, ENNReal.ofReal (W.θ z) * ENNReal.ofReal (D.edens L z) < ⊤

theorem Good.memLp (D : HodgeDatum Γ d) (W : Weights Γ) {L : Form d} (hL : Good D W L) :
    MemLp (D.wcoord W L) 2 (volume.restrict U) := by
  have hm : AEStronglyMeasurable (D.wcoord W L) (volume.restrict U) :=
    (D.continuousOn_wcoord W hL.cont).aestronglyMeasurable isOpen_U.measurableSet
  refine (memLp_two_iff_integrable_sq_norm hm).mpr ⟨(hm.norm.pow 2), ?_⟩
  have h0 : 0 ≤ᵐ[volume.restrict U] fun z => ‖D.wcoord W L z‖ ^ 2 :=
    Eventually.of_forall fun z => by positivity
  rw [hasFiniteIntegral_iff_ofReal h0]
  refine lt_of_le_of_lt (le_of_eq ?_) hL.fin
  refine lintegral_congr fun z => ?_
  rw [D.norm_wcoord_sq W, ENNReal.ofReal_mul (W.θ_nonneg z)]

theorem CptForm.memLp (D : HodgeDatum Γ d) (W : Weights Γ) {L : Form d} (hL : CptForm L) :
    MemLp (D.wcoord W L) 2 (volume.restrict U) := by
  obtain ⟨hc, K, hK, hKU, h0⟩ := hL
  refine memLp_of_cpt (D.continuousOn_wcoord W hc) hK hKU fun z hz hzK => ?_
  have e0 : mkX (0 : Wd d) 0 = 0 := rfl
  simp [HodgeDatum.wcoord, HodgeDatum.coord, h0 z hz hzK, e0]

/-- The Hilbert space of square integrable (weighted) `S`-coordinates of forms. -/
abbrev Hs (d : ℕ) := Lp (XP (Wd d)) 2 (volume.restrict U)

theorem inner_toLp_eq {f g : ℂ → XP (Wd d)} (hf : MemLp f 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U)) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ z in U, ⟪f z, g z⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z h1 h2
  rw [h1, h2]

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
