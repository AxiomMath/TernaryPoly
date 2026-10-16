module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Primitive

@[expose] public section


/-!
# Approximation of the exact part by equivariant compactly supported primitives

The closure `bSub` is the closure of the span of weighted coordinates of the differentials of the
`Approx` functions; every element of the span is again represented by such a differential
(`exists_approx_of_mem_span`).

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

namespace HodgeDatum

variable (D : HodgeDatum Γ d) (W : Weights Γ)

theorem wcoord_add (L₁ L₂ : Form d) (z : ℂ) :
    D.wcoord W (fun w => L₁ w + L₂ w) z = D.wcoord W L₁ z + D.wcoord W L₂ z := by
  rw [wcoord_eq, wcoord_eq, wcoord_eq, map_add]

theorem wcoord_sub (L₁ L₂ : Form d) (z : ℂ) :
    D.wcoord W (fun w => L₁ w - L₂ w) z = D.wcoord W L₁ z - D.wcoord W L₂ z := by
  rw [wcoord_eq, wcoord_eq, wcoord_eq, map_sub]

theorem wcoord_smul (c : ℝ) (L : Form d) (z : ℂ) :
    D.wcoord W (fun w => c • L w) z = c • D.wcoord W L z := by
  rw [wcoord_eq, wcoord_eq, map_smul]

theorem wcoord_zero (z : ℂ) : D.wcoord W (fun _ => 0) z = 0 := by
  rw [wcoord_eq, map_zero]

theorem Approx.zero : D.Approx (fun _ => 0) := by
  refine ⟨contDiffOn_const, fun γ z _ => by simp, ∅, isCompact_empty, empty_subset _, fun z _ _ => ?_⟩
  simp

theorem Approx.add {φ₁ φ₂ : ℂ → Wd d} (h₁ : D.Approx φ₁) (h₂ : D.Approx φ₂) :
    D.Approx (fun z => φ₁ z + φ₂ z) := by
  obtain ⟨c1, e1, K1, hK1, hK1U, f1⟩ := h₁
  obtain ⟨c2, e2, K2, hK2, hK2U, f2⟩ := h₂
  refine ⟨c1.add c2, fun γ z hz => ?_, K1 ∪ K2, hK1.union hK2, union_subset hK1U hK2U,
    fun z hz hfree => ?_⟩
  · simp only [e1 γ z hz, e2 γ z hz, map_add]
  · have hf1 := f1 z hz fun γ h => hfree γ (Or.inl h)
    have hf2 := f2 z hz fun γ h => hfree γ (Or.inr h)
    have d1 : DifferentiableAt ℝ φ₁ z := (c1.differentiableOn (by simp)).differentiableAt
      (isOpen_U.mem_nhds hz)
    have d2 : DifferentiableAt ℝ φ₂ z := (c2.differentiableOn (by simp)).differentiableAt
      (isOpen_U.mem_nhds hz)
    rw [fderiv_fun_add d1 d2, hf1, hf2, add_zero]

theorem Approx.smul (r : ℝ) {φ : ℂ → Wd d} (h : D.Approx φ) : D.Approx (fun z => r • φ z) := by
  obtain ⟨c1, e1, K1, hK1, hK1U, f1⟩ := h
  refine ⟨c1.const_smul r, fun γ z hz => ?_, K1, hK1, hK1U, fun z hz hfree => ?_⟩
  · simp only [e1 γ z hz]
    exact ((D.ρR γ).map_smul r _).symm
  · have d1 : DifferentiableAt ℝ φ z := (c1.differentiableOn (by simp)).differentiableAt
      (isOpen_U.mem_nhds hz)
    change fderiv ℝ (r • φ) z = 0
    rw [fderiv_const_smul d1, f1 z hz hfree, smul_zero]

theorem exists_approx_of_mem_span {y : Hs d} (hy : y ∈ Submodule.span ℝ (D.genSet W)) :
    ∃ φ : ℂ → Wd d, D.Approx φ ∧ (y : ℂ → XP (Wd d)) =ᵐ[volume.restrict U]
      D.wcoord W (fun z => fderiv ℝ φ z) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨φ, h, rfl⟩ := hy
    exact ⟨φ, h, (Good.memLp D W (Approx.good D W h)).coeFn_toLp⟩
  | zero =>
    refine ⟨fun _ => 0, Approx.zero D, ?_⟩
    filter_upwards [Lp.coeFn_zero (XP (Wd d)) 2 (volume.restrict U)] with z hz
    rw [hz]
    simp [wcoord_eq]
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨φ₁, hφ₁, e₁⟩ := h₁
    obtain ⟨φ₂, hφ₂, e₂⟩ := h₂
    refine ⟨fun z => φ₁ z + φ₂ z, Approx.add D hφ₁ hφ₂, ?_⟩
    filter_upwards [Lp.coeFn_add y₁ y₂, e₁, e₂, ae_restrict_mem isOpen_U.measurableSet] with z h h1 h2 hz
    have d1 : DifferentiableAt ℝ φ₁ z := (hφ₁.1.differentiableOn (by simp)).differentiableAt
      (isOpen_U.mem_nhds hz)
    have d2 : DifferentiableAt ℝ φ₂ z := (hφ₂.1.differentiableOn (by simp)).differentiableAt
      (isOpen_U.mem_nhds hz)
    rw [h, Pi.add_apply, h1, h2, ← wcoord_add]
    simp only [wcoord_eq]
    rw [fderiv_fun_add d1 d2]
  | smul r y _ h₁ =>
    obtain ⟨φ₁, hφ₁, e₁⟩ := h₁
    refine ⟨fun z => r • φ₁ z, Approx.smul D r hφ₁, ?_⟩
    filter_upwards [Lp.coeFn_smul r y, e₁, ae_restrict_mem isOpen_U.measurableSet] with z h h1 hz
    have d1 : DifferentiableAt ℝ φ₁ z := (hφ₁.1.differentiableOn (by simp)).differentiableAt
      (isOpen_U.mem_nhds hz)
    rw [h, Pi.smul_apply, h1, ← wcoord_smul]
    simp only [wcoord_eq]
    change _ = D.Tz W z (fderiv ℝ (r • φ₁) z)
    rw [fderiv_const_smul d1]

theorem norm_sq_Hs (f : Hs d) : ‖f‖ ^ 2 = ∫ z in U, ‖(f : ℂ → XP (Wd d)) z‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  exact real_inner_self_eq_norm_sq _

/-- The pointwise comparison between the operator norm of a form and its `S`-energy. -/
theorem norm_form_sq_le {z : ℂ} (hz : z ∈ U) {Cs : ℝ} (hCs : ‖D.Sinv z‖ ≤ Cs) (E : ℂ →L[ℝ] Wd d) :
    ‖E‖ ^ 2 ≤ 2 * Cs ^ 2 * (‖D.S z (E 1)‖ ^ 2 + ‖D.S z (E Complex.I)‖ ^ 2) := by
  have hinj : ∀ x : Wd d, ‖x‖ ≤ Cs * ‖D.S z x‖ := by
    intro x
    have := Ring.inverse_mul_cancel (D.S z) (D.S_unit z hz)
    have h2 := congrArg (fun T : Wd d →L[ℂ] Wd d => T x) this
    have h2' : D.Sinv z (D.S z x) = x := h2
    calc ‖x‖ = ‖D.Sinv z (D.S z x)‖ := by rw [h2']
      _ ≤ ‖D.Sinv z‖ * ‖D.S z x‖ := (D.Sinv z).le_opNorm _
      _ ≤ Cs * ‖D.S z x‖ := mul_le_mul_of_nonneg_right hCs (norm_nonneg _)
  have h1 := hinj (E 1)
  have h2 := hinj (E Complex.I)
  have hE : ‖E‖ ≤ ‖E 1‖ + ‖E Complex.I‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have h : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
      apply Complex.ext <;> simp
    have hr : |v.re| ≤ ‖v‖ := Complex.abs_re_le_norm v
    have hi : |v.im| ≤ ‖v‖ := Complex.abs_im_le_norm v
    calc ‖E v‖ = ‖v.re • E 1 + v.im • E Complex.I‖ := by
          rw [← E.map_smul, ← E.map_smul, ← E.map_add, ← h]
      _ ≤ |v.re| * ‖E 1‖ + |v.im| * ‖E Complex.I‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (‖E 1‖ + ‖E Complex.I‖) * ‖v‖ := by
          nlinarith [norm_nonneg (E 1), norm_nonneg (E Complex.I), norm_nonneg v]
  have hs0 : 0 ≤ Cs := (norm_nonneg _).trans hCs
  nlinarith [norm_nonneg E, norm_nonneg (E 1), norm_nonneg (E Complex.I),
    norm_nonneg (D.S z (E 1)), norm_nonneg (D.S z (E Complex.I)),
    sq_nonneg (Cs * ‖D.S z (E 1)‖ - Cs * ‖D.S z (E Complex.I)‖)]

/-- **Approximation.** If `u₀ = ω - P_B ω` is represented by `L₀`, then there are `Approx`
functions `φ j` whose differentials converge to `ω - L₀ = dΨ` in `L²` on compact sets. -/
theorem exists_approximants {Φ₁ Ψ : ℂ → Wd d} (hω : Good D W (fun z => fderiv ℝ Φ₁ z))
    {L₀ : Form d} (hL₀ : ContinuousOn L₀ U)
    (hrep : ((D.xvec W hω - D.projB W (D.xvec W hω) : Hs d) : ℂ → XP (Wd d)) =ᵐ[volume.restrict U]
      D.wcoord W L₀)
    (hΨ : ∀ z ∈ U, fderiv ℝ Ψ z = fderiv ℝ Φ₁ z - L₀ z) :
    ∃ φ : ℕ → ℂ → Wd d, (∀ j, D.Approx (φ j)) ∧ ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ z in K, ‖fderiv ℝ (φ j) z - fderiv ℝ Ψ z‖ ^ 2) atTop (𝓝 0) := by
  set x := D.xvec W hω with hx
  set P := D.projB W x with hP
  have hPmem : P ∈ closure (Submodule.span ℝ (D.genSet W) : Set (Hs d)) := by
    have := D.projB_mem W x
    unfold bSub at this
    rwa [SetLike.mem_coe.symm, Submodule.topologicalClosure_coe] at this
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp hPmem
  choose φ hφ hae using fun n => exists_approx_of_mem_span D W (hy n)
  refine ⟨φ, hφ, fun K hK hKU => ?_⟩
  -- constants on `K`
  obtain ⟨Cs, hCs⟩ := hK.exists_bound_of_continuousOn (D.continuousOn_Sinv.mono hKU)
  have hinv : ContinuousOn (fun z => (W.θ z)⁻¹) U :=
    W.continuousOn_θ.inv₀ fun z hz => (W.θ_pos hz).ne'
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn (hinv.mono hKU)
  set Cb : ℝ := 2 * Cs ^ 2 * max C2 0 with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  -- the error forms
  set E : ℕ → Form d := fun n z => fderiv ℝ (φ n) z - fderiv ℝ Ψ z with hE
  have hΨc : ContinuousOn (fun z => fderiv ℝ Ψ z) U :=
    (hω.cont.sub hL₀).congr hΨ
  have hEc : ∀ n, ContinuousOn (E n) U := fun n =>
    (continuousOn_fderiv (hφ n).1).sub hΨc
  have hid : ∀ n, ((y n - P : Hs d) : ℂ → XP (Wd d)) =ᵐ[volume.restrict U]
      D.wcoord W (E n) := by
    intro n
    filter_upwards [Lp.coeFn_sub (y n) P, hae n, Lp.coeFn_sub x P, hrep,
      (Good.memLp D W hω).coeFn_toLp, ae_restrict_mem isOpen_U.measurableSet] with z h1 h2 h3 h4 h5 hz
    have hPz : (P : ℂ → XP (Wd d)) z = (x : ℂ → XP (Wd d)) z - ((x - P : Hs d) : ℂ → XP (Wd d)) z := by
      rw [h3]; simp
    rw [h1, Pi.sub_apply, h2, hPz, h4]
    have h5' : (x : ℂ → XP (Wd d)) z = D.wcoord W (fun z => fderiv ℝ Φ₁ z) z := h5
    rw [h5']
    simp only [hE, wcoord_eq, hΨ z hz, map_sub]
  have hint : ∀ n, Integrable (fun z => ‖D.wcoord W (E n) z‖ ^ 2) (volume.restrict U) := by
    intro n
    have := (memLp_two_iff_integrable_sq_norm (Lp.stronglyMeasurable (y n - P)).aestronglyMeasurable).mp
      (Lp.memLp (y n - P))
    refine this.congr ?_
    filter_upwards [hid n] with z hz
    rw [hz]
  have hnorm : ∀ n, ∫ z in U, ‖D.wcoord W (E n) z‖ ^ 2 = ‖y n - P‖ ^ 2 := by
    intro n
    rw [norm_sq_Hs]
    refine integral_congr_ae ?_
    filter_upwards [hid n] with z hz
    rw [hz]
  have hbound : ∀ n, ∫ z in K, ‖E n z‖ ^ 2 ≤ Cb * ‖y n - P‖ ^ 2 := by
    intro n
    have hpt : ∀ z ∈ K, ‖E n z‖ ^ 2 ≤ Cb * ‖D.wcoord W (E n) z‖ ^ 2 := by
      intro z hz
      have hzU := hKU hz
      have h1 := norm_form_sq_le D hzU (hCs z hz) (E n z)
      have h2 : D.edens (E n) z = (W.θ z)⁻¹ * ‖D.wcoord W (E n) z‖ ^ 2 := by
        rw [D.norm_wcoord_sq W, ← mul_assoc, inv_mul_cancel₀ (W.θ_pos hzU).ne', one_mul]
      have h3 : (W.θ z)⁻¹ ≤ max C2 0 := by
        have := hC2 z hz
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (W.θ_nonneg z))] at this
        exact this.trans (le_max_left _ _)
      have h4 : D.edens (E n) z ≤ max C2 0 * ‖D.wcoord W (E n) z‖ ^ 2 := by
        rw [h2]
        exact mul_le_mul_of_nonneg_right h3 (by positivity)
      calc ‖E n z‖ ^ 2 ≤ 2 * Cs ^ 2 * (‖D.S z (E n z 1)‖ ^ 2 + ‖D.S z (E n z Complex.I)‖ ^ 2) := h1
        _ = 2 * Cs ^ 2 * D.edens (E n) z := rfl
        _ ≤ 2 * Cs ^ 2 * (max C2 0 * ‖D.wcoord W (E n) z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = Cb * ‖D.wcoord W (E n) z‖ ^ 2 := by rw [hCb]; ring
    have hcontW : ContinuousOn (fun z => ‖D.wcoord W (E n) z‖ ^ 2) U :=
      ((D.continuousOn_wcoord W (hEc n)).norm).pow 2
    have hcontE : ContinuousOn (fun z => ‖E n z‖ ^ 2) U := ((hEc n).norm).pow 2
    calc ∫ z in K, ‖E n z‖ ^ 2 ≤ ∫ z in K, Cb * ‖D.wcoord W (E n) z‖ ^ 2 :=
          setIntegral_mono_on ((hcontE.mono hKU).integrableOn_compact hK)
            (((hcontW.mono hKU).integrableOn_compact hK).const_mul Cb) hK.measurableSet hpt
      _ = Cb * ∫ z in K, ‖D.wcoord W (E n) z‖ ^ 2 := integral_const_mul _ _
      _ ≤ Cb * ∫ z in U, ‖D.wcoord W (E n) z‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hCb0
          exact setIntegral_mono_set (hint n) (Eventually.of_forall fun z => by positivity)
            (Eventually.of_forall hKU)
      _ = Cb * ‖y n - P‖ ^ 2 := by rw [hnorm]
  have hnn : ∀ n, 0 ≤ ∫ z in K, ‖E n z‖ ^ 2 := fun n => integral_nonneg fun z => by positivity
  have hzero : Tendsto (fun n => ‖y n - P‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hlim
  have hlim2 : Tendsto (fun n => Cb * ‖y n - P‖ ^ 2) atTop (𝓝 0) := by
    have := (hzero.pow 2).const_mul Cb
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim2 hnn hbound

end HodgeDatum

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
