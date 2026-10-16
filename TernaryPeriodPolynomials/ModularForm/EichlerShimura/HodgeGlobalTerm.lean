module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CutoffCalculus
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HyperbolicUnfold

@[expose] public section


/-!
# The cancelling term of the global integration by parts

Foundation file of the unconditional Eichler--Shimura route.  In the integration by parts `∫ χ Φ = ∫ ∂_z̄χ · W` with the cutoff
`χ = cutoff · heightCutoff T`, the term `∂_z̄ χ = θ ∂_z̄ cutoff + cutoff ∂_z̄ θ` contributes
`∫ θ W ∂_z̄ cutoff`, where `W dz` is an invariant one-form.  Unfolding along the partition of
unity and the identity `Σ_γ cutoff ∘ γ = 1` show that this integral is zero
(`integral_termF_eq_zero`); only the term with `∂_z̄ θ`, which is small, remains.

Formalized by Claude Sonnet 5.5.
-/

open Complex MeasureTheory UpperHalfPlane
open scoped ContDiff MatrixGroups
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
open TernaryPeriodPolynomials.Argument.ESFoundations.Height

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.ESFoundations.Global

theorem continuousOn_dbar {f : ℂ → ℂ} (hf : ContDiffOn ℝ 1 f U) : ContinuousOn (dbar f) U := by
  have h : ContinuousOn (fun x => fderiv ℝ f x) U :=
    hf.continuousOn_fderiv_of_isOpen isOpen_U le_rfl
  unfold dbar
  exact continuousOn_const.mul ((h.clm_apply continuousOn_const).add
    (continuousOn_const.mul (h.clm_apply continuousOn_const)))

variable {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)}

theorem cutoff_ne_zero_of_dbar_ne_zero (hR : IsCover Γ R) {z : ℂ} (hz : z ∈ U)
    (h : dbar (fun w => ((cutoff Γ R w : ℝ) : ℂ)) z ≠ 0) : cutoff Γ R z ≠ 0 := by
  intro h0
  apply h
  have hmin : IsLocalMin (cutoff Γ R) z := by
    filter_upwards [isOpen_U.mem_nhds hz] with w hw
    rw [h0]; exact cutoff_nonneg Γ R w
  have hd : DifferentiableAt ℝ (cutoff Γ R) z :=
    ((contDiffOn_cutoff Γ R hR).differentiableOn (by simp) z hz).differentiableAt
      (isOpen_U.mem_nhds hz)
  have h1 : fderiv ℝ (cutoff Γ R) z = 0 := hmin.fderiv_eq_zero
  have h2 : fderiv ℝ (fun w => ((cutoff Γ R w : ℝ) : ℂ)) z =
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ (cutoff Γ R) z) :=
    (Complex.ofRealCLM.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  unfold dbar
  rw [h2, h1]
  simp

/-- The integrand of the cancelling term of the global integration by parts. -/
def termF (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ)) (T : ℝ) (m : ℕ) (a b : ℂ → ℂ)
    (z : ℂ) : ℂ :=
  if z ∈ U then ((heightCutoff T z : ℝ) : ℂ) * pairW m a b z *
    dbar (fun w => ((cutoff Γ R w : ℝ) : ℂ)) z else 0

section TermF

variable (hR : IsCover Γ R) {T : ℝ} (hT : 1 < T) {m : ℕ} {a b : ℂ → ℂ}
  (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)

include hR hT ha hb

theorem continuousOn_termF : ContinuousOn (termF Γ R T m a b) U := by
  have h1 : ContinuousOn (fun z => ((heightCutoff T z : ℝ) : ℂ)) U :=
    (contDiffOn_heightCutoffC hT).continuousOn
  have h2 : ContinuousOn (pairW m a b) U :=
    (contDiffOn_pairW m (ha.of_le (by simp)) (hb.of_le (by simp))).continuousOn
  have h3 : ContinuousOn (dbar (fun w => ((cutoff Γ R w : ℝ) : ℂ))) U :=
    continuousOn_dbar ((contDiffOn_cutoffC hR).of_le (by simp))
  refine ((h1.mul h2).mul h3).congr fun z hz => ?_
  simp [termF, hz]

omit ha hb in
theorem termF_support : ∃ Kc : Set ℂ, IsCompact Kc ∧ Kc ⊆ U ∧
    (∀ z, termF Γ R T m a b z ≠ 0 → z ∈ Kc) ∧
    (∀ z ∈ U, cutoff Γ R z * heightCutoff T z ≠ 0 → z ∈ Kc) := by
  obtain ⟨Kc, hKc, hKU, hK⟩ := exists_compact_support Γ R hT
  refine ⟨Kc, hKc, hKU, fun z hz => ?_, hK⟩
  by_cases hzU : z ∈ U
  · simp only [termF, hzU, ite_true] at hz
    have h3 : dbar (fun w => ((cutoff Γ R w : ℝ) : ℂ)) z ≠ 0 := right_ne_zero_of_mul hz
    have h1 : heightCutoff T z ≠ 0 := by
      intro h0
      apply hz
      simp [h0]
    exact hK z hzU (mul_ne_zero (cutoff_ne_zero_of_dbar_ne_zero hR hzU h3) h1)
  · simp [termF, hzU] at hz

omit hT ha hb in
theorem termF_comp {k r : ℕ} (hm : m = k + 1 + r)
    (hA : ∀ γ ∈ Γ, ∀ z ∈ U, a (mob γ z) = den γ z ^ 2 *
      (den γ z ^ k * (starRingEnd ℂ (den γ z)) ^ (m - k)) * a z)
    (hB : ∀ γ ∈ Γ, ∀ z ∈ U, b (mob γ z) = starRingEnd ℂ (den γ z ^ 2) *
      (den γ z ^ (k + 1) * (starRingEnd ℂ (den γ z)) ^ (m - (k + 1))) * b z)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) {w : ℂ} (hw : w ∈ U) :
    termF Γ R T m a b (mob γ w) * (((mob γ w).im : ℝ) : ℂ) ^ 2 =
      (w.im : ℂ) ^ 2 * ((heightCutoff T w : ℝ) : ℂ) * pairW m a b w *
        dbar (fun u => ((cutoff Γ R (mob γ u) : ℝ) : ℂ)) w := by
  have hwU : mob γ w ∈ U := mob_mem γ w
  have hD : den γ w ≠ 0 := denom_ne_zero' γ hw
  have hDb : starRingEnd ℂ (den γ w) ≠ 0 := by simpa using hD
  have hd : DifferentiableAt ℝ (fun u => ((cutoff Γ R u : ℝ) : ℂ)) (mob γ w) :=
    (((contDiffOn_cutoffC hR).differentiableOn (by simp)) _ hwU).differentiableAt
      (isOpen_U.mem_nhds hwU)
  have hch := dbar_comp (fun u => ((cutoff Γ R u : ℝ) : ℂ)) (mob γ) (hasDerivAt_mob γ hw) hd
  have hch2 : dbar (fun u => ((cutoff Γ R (mob γ u) : ℝ) : ℂ)) w =
      starRingEnd ℂ (1 / den γ w ^ 2) * dbar (fun u => ((cutoff Γ R u : ℝ) : ℂ)) (mob γ w) := hch
  have hc1 : starRingEnd ℂ (den γ w ^ 2) * starRingEnd ℂ (1 / den γ w ^ 2) = 1 := by
    rw [← map_mul]
    have : den γ w ^ 2 * (1 / den γ w ^ 2) = 1 := by field_simp
    rw [this, map_one]
  have hch' : dbar (fun u => ((cutoff Γ R u : ℝ) : ℂ)) (mob γ w) =
      starRingEnd ℂ (den γ w ^ 2) * dbar (fun u => ((cutoff Γ R (mob γ u) : ℝ) : ℂ)) w := by
    rw [hch2]
    linear_combination (-(dbar (fun u => ((cutoff Γ R u : ℝ) : ℂ)) (mob γ w))) * hc1
  have hW := pairW_equiv hm hw (hA γ hγ w hw) (hB γ hγ w hw)
  have hθ : ((heightCutoff T (mob γ w) : ℝ) : ℂ) = ((heightCutoff T w : ℝ) : ℂ) := by
    rw [heightCutoff_mob]
  have hht : (((mob γ w).im : ℝ) : ℂ) =
      (w.im : ℂ) / (den γ w * starRingEnd ℂ (den γ w)) := ht_mob γ hw
  unfold termF
  rw [ite_eq_left hwU, hθ, hW, hch', hht]
  field_simp
  simp only [map_pow]
  ring

end TermF

theorem finsum_cutoff_inv (hR : IsCover Γ R) {u : ℂ} (hu : u ∈ U) :
    ∑ᶠ γ : Γ, cutoff Γ R (mob (γ : SL(2, ℤ)) u) = 1 := by
  have h := finsum_cutoff (Γ := Γ) (R := R) hR hu
  have h2 := finsum_comp_equiv (Equiv.inv Γ)
    (f := fun γ : Γ => cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ u))
  simp only [Equiv.inv_apply, Subgroup.coe_inv, inv_inv] at h2
  rw [h2]
  exact h

theorem sum_dbar_zero (hR : IsCover Γ R) (S : Finset Γ) {L : Set ℂ} (hLU : L ⊆ U)
    (hS : ∀ γ : Γ, (∃ u ∈ L, cutoff Γ R (mob (γ : SL(2, ℤ)) u) ≠ 0) → γ ∈ S) {w : ℂ}
    (hw : w ∈ interior L) :
    ∑ γ ∈ S, dbar (fun u => ((cutoff Γ R (mob (γ : SL(2, ℤ)) u) : ℝ) : ℂ)) w = 0 := by
  have hwU : w ∈ U := hLU (interior_subset hw)
  have hdiff : ∀ γ ∈ S, DifferentiableAt ℝ
      (fun u => ((cutoff Γ R (mob (γ : SL(2, ℤ)) u) : ℝ) : ℂ)) w := by
    intro γ _
    have hc : ContDiffOn ℝ ∞ (fun u => ((cutoff Γ R (mob (γ : SL(2, ℤ)) u) : ℝ) : ℂ)) U :=
      (contDiffOn_cutoffC hR).comp (contDiffOn_mob (γ : SL(2, ℤ))) (mapsTo_mob _)
    exact (hc.differentiableOn (by simp) w hwU).differentiableAt (isOpen_U.mem_nhds hwU)
  rw [← dbar_sum S (fun γ u => ((cutoff Γ R (mob (γ : SL(2, ℤ)) u) : ℝ) : ℂ)) hdiff]
  have hev : (fun u => ∑ γ ∈ S, ((cutoff Γ R (mob (γ : SL(2, ℤ)) u) : ℝ) : ℂ)) =ᶠ[nhds w]
      fun _ => (1 : ℂ) := by
    filter_upwards [isOpen_interior.mem_nhds hw] with u hu
    have huL := interior_subset hu
    have h1 := finsum_cutoff_inv hR (hLU huL)
    rw [finsum_eq_sum_of_support_subset _ (s := S) (fun γ hγ => hS γ ⟨u, huL, hγ⟩)] at h1
    rw [← Complex.ofReal_sum, h1]
    simp
  have : dbar (fun u => ∑ γ ∈ S, ((cutoff Γ R (mob (γ : SL(2, ℤ)) u) : ℝ) : ℂ)) w =
      dbar (fun _ => (1 : ℂ)) w := by
    unfold dbar
    rw [hev.fderiv_eq]
  rw [this, dbar_const]



theorem integrable_cutoff_mul_smul (hR : IsCover Γ R) (g : SL(2, ℤ)) {f : ℍ → ℂ}
    (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable (fun z : ℍ => (cutoff Γ R (z : ℂ) : ℂ) * f (g • z)) volume := by
  have h := integrable_cutoff_mul hR g⁻¹ hf hcs
  have hmp := measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ g) (volume : Measure ℍ)
  have h2 := hmp.integrable_comp_emb (measurableEmbedding_const_smul
    (Matrix.SpecialLinearGroup.mapGL ℝ g)) |>.mpr h
  refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
  show (cutoff Γ R ((g⁻¹ • (g • z) : ℍ) : ℂ) : ℂ) * f (g • z) = _
  rw [inv_smul_smul]

theorem integral_termF_eq_zero (hR : IsCover Γ R) {T : ℝ} (hT : 1 < T) {m k r : ℕ}
    (hm : m = k + 1 + r) {a b : ℂ → ℂ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hA : ∀ γ ∈ Γ, ∀ z ∈ U, a (mob γ z) = den γ z ^ 2 *
      (den γ z ^ k * (starRingEnd ℂ (den γ z)) ^ (m - k)) * a z)
    (hB : ∀ γ ∈ Γ, ∀ z ∈ U, b (mob γ z) = starRingEnd ℂ (den γ z ^ 2) *
      (den γ z ^ (k + 1) * (starRingEnd ℂ (den γ z)) ^ (m - (k + 1))) * b z) :
    ∫ z : ℂ, termF Γ R T m a b z = 0 := by
  obtain ⟨Kc, hKc, hKU, hKs, hKs2⟩ := termF_support (m := m) (a := a) (b := b) hR hT
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hKc isOpen_U hKU
  have hfin := finite_translates_of_isCompact Γ R hLc hLU
  set S1 := hfin.toFinset with hS1
  set S : Finset Γ := S1 ∪ S1.image (fun γ => γ⁻¹) with hSdef
  set K : ℍ → ℂ := fun z => termF Γ R T m a b (z : ℂ) * (((z.im : ℝ)) : ℂ) ^ 2 with hKdef
  have hflat : ∫ z : ℂ, termF Γ R T m a b z = ∫ z : ℍ, K z ∂volume := by
    have := integral_flat_eq_hyp (termF Γ R T m a b) (fun x hx => by simp [termF, hx])
    rw [this]
  have hKcont : Continuous K := by
    refine Continuous.mul ?_ ?_
    · exact (continuousOn_termF hR hT ha hb).comp_continuous UpperHalfPlane.continuous_coe
        (fun z => z.im_pos)
    · fun_prop
  have hKsupp : ∀ z : ℍ, K z ≠ 0 → (z : ℂ) ∈ Kc := by
    intro z hz
    exact hKs _ (left_ne_zero_of_mul hz)
  have hKcs : HasCompactSupport K := by
    have hcomp : IsCompact ((UpperHalfPlane.coe) ⁻¹' Kc) := by
      rw [UpperHalfPlane.isOpenEmbedding_coe.isInducing.isCompact_iff]
      have : UpperHalfPlane.coe '' (UpperHalfPlane.coe ⁻¹' Kc) = Kc := by
        apply Set.image_preimage_eq_of_subset
        intro x hx
        exact ⟨⟨x, hKU hx⟩, rfl⟩
      rw [this]; exact hKc
    exact HasCompactSupport.of_support_subset_isCompact hcomp (fun z hz => hKsupp z hz)
  have hS : ∀ γ : Γ, γ ∉ S → ∀ z : ℍ,
      cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) * K z = 0 := by
    intro γ hγ z
    by_contra hne
    have hK : K z ≠ 0 := right_ne_zero_of_mul hne
    have hc : cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) ≠ 0 := by
      intro h; apply hne; simp [h]
    have hzL : (z : ℂ) ∈ L := interior_subset (hKL (hKsupp z hK))
    exact hγ (Finset.mem_union_left _ (hfin.mem_toFinset.mpr ⟨z, hzL, hc⟩))
  have hunf := unfold_cutoff hR hKcont hKcs S hS
  rw [hflat, hunf]
  have hint : ∀ γ ∈ S, Integrable (fun z : ℍ => (cutoff Γ R (z : ℂ) : ℂ) *
      K ((γ : SL(2, ℤ)) • z)) volume :=
    fun γ _ => integrable_cutoff_mul_smul hR γ hKcont hKcs
  rw [← integral_finsetSum _ hint]
  have hSL : ∀ γ : Γ, (∃ u ∈ L, cutoff Γ R (mob (γ : SL(2, ℤ)) u) ≠ 0) → γ ∈ S := by
    rintro γ ⟨u, huL, hu⟩
    refine Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨γ⁻¹, hfin.mem_toFinset.mpr ⟨u, huL, ?_⟩, inv_inv γ⟩)
    simpa using hu
  have hzero : ∀ z : ℍ, ∑ γ ∈ S, (cutoff Γ R (z : ℂ) : ℂ) * K ((γ : SL(2, ℤ)) • z) = 0 := by
    intro z
    have hw : (z : ℂ) ∈ U := z.im_pos
    have h1 : ∀ γ ∈ S, (cutoff Γ R (z : ℂ) : ℂ) * K ((γ : SL(2, ℤ)) • z) =
        ((cutoff Γ R (z : ℂ) : ℂ) * (((z : ℂ).im : ℂ) ^ 2 * ((heightCutoff T z : ℝ) : ℂ) *
          pairW m a b z)) * dbar (fun u => ((cutoff Γ R (mob (γ : SL(2, ℤ)) u) : ℝ) : ℂ)) z := by
      intro γ _
      have h2 := termF_comp (T := T) (a := a) (b := b) hR hm hA hB γ.2 hw
      have h3 : K ((γ : SL(2, ℤ)) • z) = termF Γ R T m a b (mob (γ : SL(2, ℤ)) (z : ℂ)) *
          ((((mob (γ : SL(2, ℤ)) (z : ℂ)).im : ℝ)) : ℂ) ^ 2 := by
        simp only [hKdef, mob_coe]
        rfl
      rw [h3, h2]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    by_cases hz0 : cutoff Γ R (z : ℂ) * heightCutoff T z = 0
    · rcases mul_eq_zero.mp hz0 with h | h
      · simp [h]
      · simp [h]
    · have hzK : (z : ℂ) ∈ Kc := hKs2 _ hw hz0
      have hsum := sum_dbar_zero hR S hLU hSL (hKL hzK)
      rw [hsum]
      simp
  simp_rw [hzero]
  simp

end TernaryPeriodPolynomials.Argument.ESFoundations.Global
