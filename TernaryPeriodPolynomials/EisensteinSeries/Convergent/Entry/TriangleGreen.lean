module

public import Mathlib

@[expose] public section


/-!
# Green's theorem on a straight triangle

Green's theorem on the standard triangle `{(s,t) | 0 ≤ s, 0 ≤ t, s + t ≤ 1}` for `C¹` functions
with values in a Banach space (`green_stdTriangle`), by Fubini over the triangle and the
fundamental theorem of calculus in each variable, and its consequence for the affine triangle
`[y₀, y₁, y₂]` in any normed space (`stokes_affine_triangle`): for a `C¹` `F`-valued one-form `η`,
`∫_Δ dη(y₁ - y₀, y₂ - y₀) = ∫_{[y₁ y₂]} η - ∫_{[y₀ y₂]} η + ∫_{[y₀ y₁]} η`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The standard triangle `{(s,t) | 0 ≤ s, 0 ≤ t, s + t ≤ 1}`. -/
def stdTriangle : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

theorem isClosed_stdTriangle : IsClosed stdTriangle := by
  have h1 : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} := isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := isClosed_le continuous_const continuous_snd
  have h3 : IsClosed {p : ℝ × ℝ | p.1 + p.2 ≤ 1} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  exact h1.inter (h2.inter h3)

theorem stdTriangle_subset_Icc : stdTriangle ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  rintro ⟨s, t⟩ ⟨hs, ht, hst⟩
  exact ⟨⟨hs, by linarith⟩, ⟨ht, by linarith⟩⟩

theorem isCompact_stdTriangle : IsCompact stdTriangle :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_stdTriangle stdTriangle_subset_Icc

theorem measurableSet_stdTriangle : MeasurableSet stdTriangle := isClosed_stdTriangle.measurableSet

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Iterated integral over the triangle, `s` inner. -/
theorem integral_stdTriangle_s_inner (f : ℝ × ℝ → F) (hf : ContinuousOn f stdTriangle) :
    ∫ p in stdTriangle, f p = ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..(1 - t), f (s, t) := by
  have hint : IntegrableOn f stdTriangle := hf.integrableOn_compact isCompact_stdTriangle
  rw [← integral_indicator measurableSet_stdTriangle, Measure.volume_eq_prod,
    integral_prod_symm _ ((integrable_indicator_iff measurableSet_stdTriangle).mpr hint)]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem ht, intervalIntegral.integral_of_le (by linarith [ht.2]),
      ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    by_cases hs : s ∈ Icc (0 : ℝ) (1 - t)
    · have : (s, t) ∈ stdTriangle := ⟨hs.1, ht.1, by linarith [hs.2]⟩
      rw [indicator_of_mem hs, indicator_of_mem this]
    · have : (s, t) ∉ stdTriangle := fun h => hs ⟨h.1, by linarith [h.2.2]⟩
      rw [indicator_of_notMem hs, indicator_of_notMem this]
  · rw [indicator_of_notMem ht]
    have : ∀ s : ℝ, (s, t) ∉ stdTriangle := fun s h => ht ⟨h.2.1, by linarith [h.1, h.2.2]⟩
    simp [indicator_of_notMem (this _)]

omit [CompleteSpace F] in
/-- Iterated integral over the triangle, `t` inner. -/
theorem integral_stdTriangle_t_inner (f : ℝ × ℝ → F) (hf : ContinuousOn f stdTriangle) :
    ∫ p in stdTriangle, f p = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..(1 - s), f (s, t) := by
  have hint : IntegrableOn f stdTriangle := hf.integrableOn_compact isCompact_stdTriangle
  rw [← integral_indicator measurableSet_stdTriangle, Measure.volume_eq_prod,
    integral_prod _ ((integrable_indicator_iff measurableSet_stdTriangle).mpr hint)]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hs, intervalIntegral.integral_of_le (by linarith [hs.2]),
      ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    by_cases ht : t ∈ Icc (0 : ℝ) (1 - s)
    · have : (s, t) ∈ stdTriangle := ⟨hs.1, ht.1, by linarith [ht.2]⟩
      rw [indicator_of_mem ht, indicator_of_mem this]
    · have : (s, t) ∉ stdTriangle := fun h => ht ⟨h.2.1, by linarith [h.2.2]⟩
      rw [indicator_of_notMem ht, indicator_of_notMem this]
  · rw [indicator_of_notMem hs]
    have : ∀ t : ℝ, (s, t) ∉ stdTriangle := fun t h => hs ⟨h.1, by linarith [h.2.1, h.2.2]⟩
    simp [indicator_of_notMem (this _)]

/-! ### Green's theorem on the standard triangle -/

section Green

variable (P Q : ℝ × ℝ → F) {U : Set (ℝ × ℝ)}

omit [CompleteSpace F] in
theorem hasDerivAt_fst_slice (hU : IsOpen U) (hQ : ContDiffOn ℝ 1 Q U) {p : ℝ × ℝ} (hp : p ∈ U) :
    HasDerivAt (fun s : ℝ => Q (s, p.2)) (fderiv ℝ Q p ((1 : ℝ), (0 : ℝ))) p.1 := by
  have hd : HasFDerivAt Q (fderiv ℝ Q p) p :=
    ((hQ.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)).hasFDerivAt
  have hs : HasDerivAt (fun s : ℝ => (s, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact hd.comp_hasDerivAt p.1 (by simpa using hs)

omit [CompleteSpace F] in
theorem hasDerivAt_snd_slice (hU : IsOpen U) (hP : ContDiffOn ℝ 1 P U) {p : ℝ × ℝ} (hp : p ∈ U) :
    HasDerivAt (fun t : ℝ => P (p.1, t)) (fderiv ℝ P p ((0 : ℝ), (1 : ℝ))) p.2 := by
  have hd : HasFDerivAt P (fderiv ℝ P p) p :=
    ((hP.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)).hasFDerivAt
  have hs : HasDerivAt (fun t : ℝ => (p.1, t)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact hd.comp_hasDerivAt p.2 (by simpa using hs)

omit [CompleteSpace F] in
theorem continuousOn_fderiv_apply (hU : IsOpen U) (hQ : ContDiffOn ℝ 1 Q U) (v : ℝ × ℝ) :
    ContinuousOn (fun p => fderiv ℝ Q p v) U :=
  (hQ.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const

/-- **Green's theorem on the standard triangle** for `C¹` functions `P, Q` on an open neighbourhood `U` of it:
`∬_Δ (∂Q/∂s - ∂P/∂t) ds dt = ∫₀¹ (Q(1-t,t) - Q(0,t)) dt - ∫₀¹ (P(s,1-s) - P(s,0)) ds`. -/
theorem green_stdTriangle {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (P Q : ℝ × ℝ → F) (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hT : stdTriangle ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    ∫ p in stdTriangle, (fderiv ℝ Q p (1, 0) - fderiv ℝ P p (0, 1)) =
      (∫ t in (0 : ℝ)..1, (Q (1 - t, t) - Q (0, t))) -
        ∫ s in (0 : ℝ)..1, (P (s, 1 - s) - P (s, 0)) := by
  have hc1 : ContinuousOn (fun p => fderiv ℝ Q p ((1 : ℝ), (0 : ℝ))) stdTriangle :=
    (continuousOn_fderiv_apply Q hU hQ _).mono hT
  have hc2 : ContinuousOn (fun p => fderiv ℝ P p ((0 : ℝ), (1 : ℝ))) stdTriangle :=
    (continuousOn_fderiv_apply P hU hP _).mono hT
  have hi1 : IntegrableOn (fun p => fderiv ℝ Q p ((1 : ℝ), (0 : ℝ))) stdTriangle :=
    ContinuousOn.integrableOn_compact isCompact_stdTriangle hc1
  have hi2 : IntegrableOn (fun p => fderiv ℝ P p ((0 : ℝ), (1 : ℝ))) stdTriangle :=
    ContinuousOn.integrableOn_compact isCompact_stdTriangle hc2
  rw [integral_sub hi1 hi2, integral_stdTriangle_s_inner _ hc1, integral_stdTriangle_t_inner _ hc2]
  congr 1
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have hle : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
    have hmem : ∀ s ∈ uIcc (0 : ℝ) (1 - t), (s, t) ∈ U := fun s hs => by
      rw [uIcc_of_le hle] at hs
      exact hT ⟨hs.1, ht.1, by linarith [hs.2]⟩
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s' : ℝ => Q (s', t))
      (f' := fun s' : ℝ => fderiv ℝ Q (s', t) ((1 : ℝ), (0 : ℝ))) (fun s hs => ?_) ?_
    · exact hasDerivAt_fst_slice Q hU hQ (p := (s, t)) (hmem s hs)
    · refine ContinuousOn.intervalIntegrable ?_
      exact (continuousOn_fderiv_apply Q hU hQ ((1 : ℝ), (0 : ℝ))).comp
        (Continuous.continuousOn (by fun_prop)) (fun s hs => hmem s hs)
  · refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have hle : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
    have hmem : ∀ t ∈ uIcc (0 : ℝ) (1 - s), (s, t) ∈ U := fun t ht => by
      rw [uIcc_of_le hle] at ht
      exact hT ⟨hs.1, ht.1, by linarith [ht.2]⟩
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t' : ℝ => P (s, t'))
      (f' := fun t' : ℝ => fderiv ℝ P (s, t') ((0 : ℝ), (1 : ℝ))) (fun t ht => ?_) ?_
    · exact hasDerivAt_snd_slice P hU hP (p := (s, t)) (hmem t ht)
    · refine ContinuousOn.intervalIntegrable ?_
      exact (continuousOn_fderiv_apply P hU hP ((0 : ℝ), (1 : ℝ))).comp
        (Continuous.continuousOn (by fun_prop)) (fun t ht => hmem t ht)

end Green

/-! ### Stokes on an affine triangle -/

section Stokes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integral of a 1-form `η : E → E →L[ℝ] F` along the segment `x → y`. -/
def segmentIntegral {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (η : E → E →L[ℝ] F) (x y : E) : F :=
  ∫ t in (0 : ℝ)..1, η (x + t • (y - x)) (y - x)

/-- The affine parametrisation `σ(s,t) = y₀ + s(y₁ - y₀) + t(y₂ - y₀)` of the triangle. -/
def affTri (y₀ y₁ y₂ : E) (p : ℝ × ℝ) : E := y₀ + p.1 • (y₁ - y₀) + p.2 • (y₂ - y₀)

/-- The linear part of `affTri`. -/
def affTriLin (a b : E) : ℝ × ℝ →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight b

theorem affTriLin_apply (a b : E) (p : ℝ × ℝ) : affTriLin a b p = p.1 • a + p.2 • b := rfl

theorem hasFDerivAt_affTri (y₀ y₁ y₂ : E) (p : ℝ × ℝ) :
    HasFDerivAt (affTri y₀ y₁ y₂) (affTriLin (y₁ - y₀) (y₂ - y₀)) p := by
  have h : affTri y₀ y₁ y₂ = fun q => y₀ + affTriLin (y₁ - y₀) (y₂ - y₀) q := by
    funext q
    simp only [affTri, affTriLin_apply, add_assoc]
  rw [h]
  exact (affTriLin (y₁ - y₀) (y₂ - y₀)).hasFDerivAt.const_add y₀

theorem contDiff_affTri (y₀ y₁ y₂ : E) : ContDiff ℝ 1 (affTri y₀ y₁ y₂) := by
  unfold affTri
  fun_prop

theorem continuous_affTri (y₀ y₁ y₂ : E) : Continuous (affTri y₀ y₁ y₂) :=
  (contDiff_affTri y₀ y₁ y₂).continuous

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_apply_affTri (η : E → E →L[ℝ] F) (U : Set E) (hU : IsOpen U)
    (hη : ContDiffOn ℝ 1 η U) (y₀ y₁ y₂ : E) {p : ℝ × ℝ} (hp : affTri y₀ y₁ y₂ p ∈ U) (v : E)
    (w : ℝ × ℝ) :
    fderiv ℝ (fun q => η (affTri y₀ y₁ y₂ q) v) p w =
      fderiv ℝ η (affTri y₀ y₁ y₂ p) (affTriLin (y₁ - y₀) (y₂ - y₀) w) v := by
  have h1 : HasFDerivAt η (fderiv ℝ η (affTri y₀ y₁ y₂ p)) (affTri y₀ y₁ y₂ p) :=
    ((hη.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)).hasFDerivAt
  have h2 := h1.comp p (hasFDerivAt_affTri y₀ y₁ y₂ p)
  have h3 := (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp p h2
  rw [show (fun q => η (affTri y₀ y₁ y₂ q) v) =
    (ContinuousLinearMap.apply ℝ F v) ∘ (η ∘ affTri y₀ y₁ y₂) from rfl, h3.fderiv]
  rfl

/-- **Stokes for the affine triangle `[y₀, y₁, y₂]`**:
`∫_Δ (dη)(y₁ - y₀, y₂ - y₀) ds dt = ∮_{∂[y₀y₁y₂]} η`, where `(dη)(u,v) = D_uη(v) - D_vη(u)`. -/
theorem stokes_affine_triangle {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (η : E → E →L[ℝ] F) (U : Set E) (hU : IsOpen U) (hη : ContDiffOn ℝ 1 η U) (y₀ y₁ y₂ : E)
    (hT : ∀ p ∈ stdTriangle, y₀ + p.1 • (y₁ - y₀) + p.2 • (y₂ - y₀) ∈ U) :
    ∫ p in stdTriangle,
        (fderiv ℝ η (y₀ + p.1 • (y₁ - y₀) + p.2 • (y₂ - y₀)) (y₁ - y₀) (y₂ - y₀) -
          fderiv ℝ η (y₀ + p.1 • (y₁ - y₀) + p.2 • (y₂ - y₀)) (y₂ - y₀) (y₁ - y₀)) =
      segmentIntegral η y₁ y₂ - segmentIntegral η y₀ y₂ + segmentIntegral η y₀ y₁ := by
  set σ := affTri y₀ y₁ y₂ with hσ
  set U' : Set (ℝ × ℝ) := σ ⁻¹' U with hU'
  have hU'o : IsOpen U' := hU.preimage (continuous_affTri y₀ y₁ y₂)
  have hTU' : stdTriangle ⊆ U' := fun p hp => hT p hp
  have hcomp : ContDiffOn ℝ 1 (fun p => η (σ p)) U' :=
    hη.comp (contDiff_affTri y₀ y₁ y₂).contDiffOn (fun p hp => hp)
  set P : ℝ × ℝ → F := fun p => η (σ p) (y₁ - y₀) with hP
  set Q : ℝ × ℝ → F := fun p => η (σ p) (y₂ - y₀) with hQ
  have hPd : ContDiffOn ℝ 1 P U' := hcomp.clm_apply contDiffOn_const
  have hQd : ContDiffOn ℝ 1 Q U' := hcomp.clm_apply contDiffOn_const
  have hG := green_stdTriangle P Q U' hU'o hTU' hPd hQd
  have hint : ∫ p in stdTriangle,
        (fderiv ℝ η (y₀ + p.1 • (y₁ - y₀) + p.2 • (y₂ - y₀)) (y₁ - y₀) (y₂ - y₀) -
          fderiv ℝ η (y₀ + p.1 • (y₁ - y₀) + p.2 • (y₂ - y₀)) (y₂ - y₀) (y₁ - y₀)) =
      ∫ p in stdTriangle, (fderiv ℝ Q p (1, 0) - fderiv ℝ P p (0, 1)) := by
    refine setIntegral_congr_fun measurableSet_stdTriangle (fun p hp => ?_)
    have hpU : σ p ∈ U := hT p hp
    have e1 : fderiv ℝ Q p (1, 0) = fderiv ℝ η (σ p) (y₁ - y₀) (y₂ - y₀) := by
      rw [hQ]
      rw [fderiv_apply_affTri η U hU hη y₀ y₁ y₂ hpU,
        show affTriLin (y₁ - y₀) (y₂ - y₀) ((1 : ℝ), (0 : ℝ)) = y₁ - y₀ by
          simp [affTriLin_apply]]
    have e2 : fderiv ℝ P p (0, 1) = fderiv ℝ η (σ p) (y₂ - y₀) (y₁ - y₀) := by
      rw [hP]
      rw [fderiv_apply_affTri η U hU hη y₀ y₁ y₂ hpU,
        show affTriLin (y₁ - y₀) (y₂ - y₀) ((0 : ℝ), (1 : ℝ)) = y₂ - y₀ by
          simp [affTriLin_apply]]
    rw [e1, e2]
    rfl
  rw [hint, hG]
  have hcQ : ContinuousOn Q U' := hQd.continuousOn
  have hcP : ContinuousOn P U' := hPd.continuousOn
  have hI1 : ∀ t ∈ uIcc (0 : ℝ) 1, (1 - t, t) ∈ U' := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    exact hTU' ⟨by linarith [ht.2], ht.1, by linarith⟩
  have hI0 : ∀ t ∈ uIcc (0 : ℝ) 1, ((0 : ℝ), t) ∈ U' := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    exact hTU' ⟨le_rfl, ht.1, by linarith [ht.2]⟩
  have hJ1 : ∀ s ∈ uIcc (0 : ℝ) 1, (s, 1 - s) ∈ U' := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    exact hTU' ⟨hs.1, by linarith [hs.2], by linarith⟩
  have hJ0 : ∀ s ∈ uIcc (0 : ℝ) 1, (s, (0 : ℝ)) ∈ U' := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    exact hTU' ⟨hs.1, le_rfl, by linarith [hs.2]⟩
  have iQ1 : IntervalIntegrable (fun t : ℝ => Q (1 - t, t)) volume 0 1 :=
    (hcQ.comp (Continuous.continuousOn (by fun_prop)) hI1).intervalIntegrable
  have iP1' : IntervalIntegrable (fun t : ℝ => P (1 - t, t)) volume 0 1 :=
    (hcP.comp (Continuous.continuousOn (by fun_prop)) hI1).intervalIntegrable
  have iQ0 : IntervalIntegrable (fun t : ℝ => Q (0, t)) volume 0 1 :=
    (hcQ.comp (Continuous.continuousOn (by fun_prop)) hI0).intervalIntegrable
  have iP1 : IntervalIntegrable (fun s : ℝ => P (s, 1 - s)) volume 0 1 :=
    (hcP.comp (Continuous.continuousOn (by fun_prop)) hJ1).intervalIntegrable
  have iP0 : IntervalIntegrable (fun s : ℝ => P (s, 0)) volume 0 1 :=
    (hcP.comp (Continuous.continuousOn (by fun_prop)) hJ0).intervalIntegrable
  have e12 : segmentIntegral η y₁ y₂ = ∫ t in (0 : ℝ)..1, (Q (1 - t, t) - P (1 - t, t)) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hσ1 : σ (1 - t, t) = y₁ + t • (y₂ - y₁) := by
      simp only [hσ, affTri]
      module
    simp only [hQ, hP, hσ1]
    rw [← map_sub, sub_sub_sub_cancel_right]
  have e02 : segmentIntegral η y₀ y₂ = ∫ t in (0 : ℝ)..1, Q (0, t) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hσ1 : σ (0, t) = y₀ + t • (y₂ - y₀) := by
      simp only [hσ, affTri]
      module
    simp only [hQ, hσ1]
  have e01 : segmentIntegral η y₀ y₁ = ∫ s in (0 : ℝ)..1, P (s, 0) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hσ1 : σ (s, 0) = y₀ + s • (y₁ - y₀) := by
      simp only [hσ, affTri]
      module
    simp only [hP, hσ1]
  have hsub : ∫ t in (0 : ℝ)..1, P (1 - t, t) = ∫ s in (0 : ℝ)..1, P (s, 1 - s) := by
    have h := intervalIntegral.integral_comp_sub_left (fun s : ℝ => P (s, 1 - s)) (a := (0 : ℝ))
      (b := 1) 1
    simp only [sub_sub_cancel, sub_self, sub_zero] at h
    exact h
  rw [intervalIntegral.integral_sub iQ1 iQ0, intervalIntegral.integral_sub iP1 iP0, e12, e02, e01,
    intervalIntegral.integral_sub iQ1 iP1', hsub]
  abel

end Stokes

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
