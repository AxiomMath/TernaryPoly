module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HeightCutoff
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Wirtinger

@[expose] public section


/-!
# Calculus for the truncated cutoffs of the global integration by parts

Foundation file of the unconditional Eichler--Shimura route.  The chain rule `∂_z̄ (f ∘ g) = conj g' · (∂_z̄ f) ∘ g` for holomorphic `g`
(`dbar_comp`); the truncated partition of unity `chi T = cutoff · heightCutoff T` is smooth with
compact support in the upper half plane (`chi_regular`) and has the product-rule derivative
(`dbar_chi`); the transformation of the boundary field `pairW` of the Hodge pair under a
translate (`pairW_equiv`).

Formalized by Claude Sonnet 5.5.
-/

open Complex MeasureTheory
open scoped ContDiff MatrixGroups
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
open TernaryPeriodPolynomials.Argument.ESFoundations.Height

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.ESFoundations.Global

/-- A real-linear map of `ℂ` splits into its `∂` and `∂̄` parts. -/
theorem real_linear_decomp (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    L v = ((1 / 2 : ℂ) * (L 1 - I * L I)) * v +
      ((1 / 2 : ℂ) * (L 1 + I * L I)) * starRingEnd ℂ v := by
  have hv : v = (v.re : ℂ) * 1 + (v.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have h1 : L v = (v.re : ℝ) • L 1 + (v.im : ℝ) • L I := by
    conv_lhs => rw [hv]
    have : ((v.re : ℂ) * 1 + (v.im : ℂ) * I) = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • I := by
      simp [Complex.real_smul]
    rw [this, map_add, map_smul, map_smul]
  rw [h1, Complex.real_smul, Complex.real_smul]
  have hr : (v.re : ℂ) = (v + starRingEnd ℂ v) / 2 := by
    apply Complex.ext <;> simp
  have hi : (v.im : ℂ) = (v - starRingEnd ℂ v) / (2 * I) := by
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im]
    ring
  rw [hr, hi]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

theorem dbar_comp (f g : ℂ → ℂ) {z g' : ℂ} (hg : HasDerivAt g g' z)
    (hf : DifferentiableAt ℝ f (g z)) :
    dbar (fun w => f (g w)) z = starRingEnd ℂ g' * dbar f (g z) := by
  have hc := hf.hasFDerivAt.comp z (hg.hasFDerivAt.restrictScalars ℝ)
  have h1 : fderiv ℝ (fun w => f (g w)) z =
      (fderiv ℝ f (g z)).comp ((ContinuousLinearMap.toSpanSingleton ℂ g').restrictScalars ℝ) :=
    hc.fderiv
  unfold dbar
  rw [h1]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  rw [real_linear_decomp (fderiv ℝ f (g z)) (1 * g'),
    real_linear_decomp (fderiv ℝ f (g z)) (I * g')]
  simp only [map_mul, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Extension by zero of a function smooth on `U` with support in a compact subset of `U`. -/
theorem contDiff_extend {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (hsupp : ∀ z ∈ U, f z ≠ 0 → z ∈ K) :
    ContDiff ℝ ∞ (fun z => if z ∈ U then f z else 0) ∧
      HasCompactSupport (fun z => if z ∈ U then f z else 0) ∧
      tsupport (fun z => if z ∈ U then f z else 0) ⊆ U := by
  have hsub : Function.support (fun z => if z ∈ U then f z else 0) ⊆ K := by
    intro z hz
    by_cases hzU : z ∈ U
    · simp only [Function.mem_support, hzU, ite_true] at hz
      exact hsupp z hzU hz
    · simp [Function.mem_support, hzU] at hz
  have hts : tsupport (fun z => if z ∈ U then f z else 0) ⊆ K :=
    closure_minimal hsub hK.isClosed
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK hsub, hts.trans hKU⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hzU : z ∈ U
  · have : ContDiffAt ℝ ∞ f z := hf.contDiffAt (isOpen_U.mem_nhds hzU)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_U.mem_nhds hzU] with w hw
    simp [hw]
  · have hzK : z ∉ K := fun h => hzU (hKU h)
    have : (fun w => if w ∈ U then f w else 0) =ᶠ[nhds z] fun _ => (0 : ℂ) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
      by_cases hwU : w ∈ U
      · have : f w = 0 := by
          by_contra hne
          exact hw (hsupp w hwU hne)
        simp [hwU, this]
      · simp [hwU]
    exact (contDiffAt_const).congr_of_eventuallyEq this

section Cut

variable (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ))

theorem exists_compact_support {T : ℝ} (hT : 1 < T) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ ∀ z ∈ U, cutoff Γ R z * heightCutoff T z ≠ 0 → z ∈ K := by
  set B : Set ℂ := (Set.Icc (-1 : ℝ) 1) ×ℂ (Set.Icc (1 / 2 : ℝ) (T ^ 2)) with hB
  have hBc : IsCompact B := isCompact_Icc.reProdIm isCompact_Icc
  have hBU : B ⊆ U := by
    intro w hw
    rw [hB, Complex.mem_reProdIm] at hw
    show 0 < w.im
    linarith [hw.2.1]
  refine ⟨⋃ r ∈ R, (mob r⁻¹) '' B, ?_, ?_, ?_⟩
  · refine R.isCompact_biUnion fun r _ => hBc.image_of_continuousOn ?_
    exact (contDiffOn_mob (r⁻¹) (n := 0)).continuousOn.mono hBU
  · intro z hz
    obtain ⟨r, -, w, -, rfl⟩ := Set.mem_iUnion₂.mp hz
    exact mob_mem _ _
  · intro z hz hne
    have h1 : cutoff Γ R z ≠ 0 := left_ne_zero_of_mul hne
    have h2 : heightCutoff T z ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨r, hr, hre, him⟩ := mem_siegel_of_cutoff_ne_zero Γ R h1
    have hup : (mob r z).im < T ^ 2 :=
      lt_of_le_of_lt (im_mob_le_height r z) (height_lt_of_heightCutoff_ne_zero hT h2)
    refine Set.mem_iUnion₂.mpr ⟨r, hr, mob r z, ?_, ?_⟩
    · rw [hB, Complex.mem_reProdIm]
      exact ⟨abs_le.mp hre, him, hup.le⟩
    · rw [← mob_mul, inv_mul_cancel, mob_one hz]

/-- The truncated partition cutoff, extended by zero off `U`. -/
def chi (T : ℝ) (z : ℂ) : ℂ :=
  if z ∈ U then ((cutoff Γ R z * heightCutoff T z : ℝ) : ℂ) else 0

variable {Γ R}

theorem contDiffOn_cutoffC (hR : IsCover Γ R) :
    ContDiffOn ℝ ∞ (fun z => ((cutoff Γ R z : ℝ) : ℂ)) U :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_cutoff Γ R hR)

theorem contDiffOn_heightCutoffC {T : ℝ} (hT : 1 < T) :
    ContDiffOn ℝ ∞ (fun z => ((heightCutoff T z : ℝ) : ℂ)) U :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_heightCutoff hT)

theorem chi_regular (hR : IsCover Γ R) {T : ℝ} (hT : 1 < T) :
    ContDiff ℝ ∞ (chi Γ R T) ∧ HasCompactSupport (chi Γ R T) ∧ tsupport (chi Γ R T) ⊆ U := by
  obtain ⟨K, hKc, hKU, hK⟩ := exists_compact_support Γ R hT
  have hf : ContDiffOn ℝ ∞ (fun z => ((cutoff Γ R z * heightCutoff T z : ℝ) : ℂ)) U := by
    simpa using (contDiffOn_cutoffC hR).mul (contDiffOn_heightCutoffC hT)
  exact contDiff_extend hKc hKU hf (fun z hz hne => hK z hz (by
    intro h; apply hne; simp [h]))

theorem dbar_chi (hR : IsCover Γ R) {T : ℝ} (hT : 1 < T) {z : ℂ} (hz : z ∈ U) :
    dbar (chi Γ R T) z = ((heightCutoff T z : ℝ) : ℂ) * dbar (fun w => ((cutoff Γ R w : ℝ) : ℂ)) z +
      ((cutoff Γ R z : ℝ) : ℂ) * dbar (fun w => ((heightCutoff T w : ℝ) : ℂ)) z := by
  have h1 : chi Γ R T =ᶠ[nhds z]
      fun w => ((cutoff Γ R w : ℝ) : ℂ) * ((heightCutoff T w : ℝ) : ℂ) := by
    filter_upwards [isOpen_U.mem_nhds hz] with w hw
    simp [chi, hw]
  have hd1 : DifferentiableAt ℝ (fun w => ((cutoff Γ R w : ℝ) : ℂ)) z :=
    ((contDiffOn_cutoffC hR).differentiableOn (by simp) z hz).differentiableAt
      (isOpen_U.mem_nhds hz)
  have hd2 : DifferentiableAt ℝ (fun w => ((heightCutoff T w : ℝ) : ℂ)) z :=
    ((contDiffOn_heightCutoffC hT).differentiableOn (by simp) z hz).differentiableAt
      (isOpen_U.mem_nhds hz)
  have : dbar (chi Γ R T) z = dbar (fun w => ((cutoff Γ R w : ℝ) : ℂ) *
      ((heightCutoff T w : ℝ) : ℂ)) z := by
    unfold dbar
    rw [h1.fderiv_eq]
  rw [this, dbar_mul hd1 hd2]
  ring

theorem pairW_core (k r : ℕ) (D Db y A Bc : ℂ) (hD : D ≠ 0) (hDb : Db ≠ 0) :
    2 * I * (y / (D * Db)) ^ (k + 1 + r + 1) *
        (D ^ 2 * (D ^ k * Db ^ (r + 1)) * A) * (D ^ 2 * (Db ^ (k + 1) * D ^ r) * Bc) =
      D ^ 2 * (2 * I * y ^ (k + 1 + r + 1) * (A * Bc)) := by
  rw [div_pow, mul_pow]
  field_simp
  ring

/-- The denominator of the translate, and its conjugate. -/
def den (γ : SL(2, ℤ)) (z : ℂ) : ℂ := ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)

theorem conj_den (γ : SL(2, ℤ)) (z : ℂ) :
    starRingEnd ℂ (den γ z) = ((γ 1 0 : ℤ) : ℂ) * starRingEnd ℂ z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [den]

theorem ht_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ U) :
    ht (mob γ z) = ht z / (den γ z * starRingEnd ℂ (den γ z)) := by
  have h := norm_denom_sq γ hz
  unfold ht
  rw [h, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem pairW_equiv {m k r : ℕ} (hm : m = k + 1 + r) {a b : ℂ → ℂ} {γ : SL(2, ℤ)} {z : ℂ}
    (hz : z ∈ U)
    (hA : a (mob γ z) = den γ z ^ 2 * (den γ z ^ k * (starRingEnd ℂ (den γ z)) ^ (m - k)) * a z)
    (hB : b (mob γ z) = starRingEnd ℂ (den γ z ^ 2) *
      (den γ z ^ (k + 1) * (starRingEnd ℂ (den γ z)) ^ (m - (k + 1))) * b z) :
    pairW m a b (mob γ z) = den γ z ^ 2 * pairW m a b z := by
  have hD : den γ z ≠ 0 := denom_ne_zero' γ hz
  have hDb : starRingEnd ℂ (den γ z) ≠ 0 := by simpa using hD
  subst hm
  have e1 : k + 1 + r - k = r + 1 := by omega
  have e2 : k + 1 + r - (k + 1) = r := by omega
  rw [e1] at hA
  rw [e2] at hB
  unfold pairW
  rw [ht_mob γ hz, hA, hB]
  simp only [map_mul, map_pow, Complex.conj_conj]
  have := pairW_core k r (den γ z) (starRingEnd ℂ (den γ z)) (ht z) (a z)
    (starRingEnd ℂ (b z)) hD hDb
  linear_combination this

end Cut

end TernaryPeriodPolynomials.Argument.ESFoundations.Global
