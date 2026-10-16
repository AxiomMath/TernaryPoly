module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.LocalOperators
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Unfold
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Hilbert
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.LocalMollify
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Linear

@[expose] public section



/-! # General coercivity, Tier B: the average intertwines the differential and codifferential

The normalized pullback `actPull` is linear over invariant scalars and commutes with `d` and `δ`;
hence the average `Π g = ∑_γ γ* g` of a compactly supported smooth form commutes with `d` and `δ`.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set MeasureTheory Filter Topology TernaryPoly TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham
  TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormConnection
  TernaryPoly.SymmetricSpaceRiemannian
open scoped ContDiff

variable {Γ : Subgroup RealGL} {n k : ℕ}

theorem actPull_fun_smul (n k : ℕ) (γ : RealGL) (u : Coordinates → ℝ)
    (w : Coordinates → FormValue n k) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    actPull n k γ (fun y => u y • w y) x = u (coordinateAction γ x) • actPull n k γ w x :=
  (actPull_apply n k γ _ hx).trans
    ((realFormPullback_smul n k γ x (u (coordinateAction γ x)) (w (coordinateAction γ x))).trans
      (congrArg (fun z : FormValue n k => u (coordinateAction γ x) • z)
        (actPull_apply n k γ w hx).symm))

theorem extDeriv_finset_sum {ι : Type*} (s : Finset ι) (h : ι → Coordinates → FormValue n k)
    {x : Coordinates} (hd : ∀ i ∈ s, DifferentiableAt ℝ (h i) x) :
    extDeriv (fun y => ∑ i ∈ s, h i y) x = ∑ i ∈ s, extDeriv (h i) x := by
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Coordinates (PolynomialCoefficientMetric.Coefficients n)
    (n := k)) (fderiv ℝ (fun y => ∑ i ∈ s, h i y) x) = ∑ i ∈ s,
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Coordinates (PolynomialCoefficientMetric.Coefficients n)
        (n := k)) (fderiv ℝ (h i) x)
  rw [fderiv_fun_sum hd, TernaryPoly.PolynomialFormCoordinates.clm_map_sum]

theorem extDeriv_mem_Cc {g : Coordinates → FormValue n k} (hg : g ∈ Cc n k) :
    extDeriv g ∈ Cc (n := n) (k + 1) :=
  ⟨contDiffOn_univ.mp (smooth_extDeriv isOpen_univ hg.1.contDiffOn),
    hg.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_extDeriv_subset n k g),
    (tsupport_extDeriv_subset n k g).trans hg.2.2⟩

theorem localAdjoint_mem_Cc {g : Coordinates → FormValue n (k + 1)} (hg : g ∈ Cc n (k + 1)) :
    localAdjoint n k g ∈ Cc (n := n) k :=
  ⟨contDiff_localAdjoint n k hg.1.contDiffOn hg.2.2,
    hasCompactSupport_localAdjoint n k g hg.2.1,
    (tsupport_localAdjoint n k g).trans hg.2.2⟩

theorem localAdjoint_zero_apply {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    localAdjoint n k (0 : Coordinates → FormValue n (k + 1)) x = 0 := by
  have h := localAdjoint_smul n k 0 (w := (0 : Coordinates → FormValue n (k + 1)))
    contDiffOn_const hx
  have e : (0 : ℝ) • (0 : Coordinates → FormValue n (k + 1)) = 0 :=
    funext fun y => zero_smul_fv _
  rw [e] at h
  exact h.trans (zero_smul_fv _)

theorem localAdjoint_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (h : ι → Coordinates → FormValue n (k + 1))
    (hh : ∀ i ∈ s, ContDiffOn ℝ ∞ (h i) positiveCoordinates) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    localAdjoint n k (fun y => ∑ i ∈ s, h i y) x = ∑ i ∈ s, localAdjoint n k (h i) x := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact localAdjoint_zero_apply hx
  | insert j s hj ih =>
    have hs : ∀ i ∈ s, ContDiffOn ℝ ∞ (h i) positiveCoordinates :=
      fun i hi => hh i (Finset.mem_insert_of_mem hi)
    have hsum : ContDiffOn ℝ ∞ (fun y => ∑ i ∈ s, h i y) positiveCoordinates :=
      ContDiffOn.sum (fun i hi => hs i hi)
    have e : (fun y => ∑ i ∈ insert j s, h i y) = h j + fun y => ∑ i ∈ s, h i y :=
      funext fun y => Finset.sum_insert hj
    rw [e, Finset.sum_insert hj]
    have := localAdjoint_add n k (hh j (Finset.mem_insert_self j s)) hsum hx
    exact this.trans (congrArg (fun z => localAdjoint n k (h j) x + z) (ih hs))

theorem Admissible.extDeriv_actSum (h : Admissible Γ) {g : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    extDeriv (actSum Γ n k g) x = actSum Γ n (k + 1) (extDeriv g) x := by
  classical
  obtain ⟨N, hN, hNp, hfin⟩ := h.translates_locallyFinite hg.2.1 hg.2.2 x hx
  let A : Finset Γ := hfin.toFinset
  have hloc : actSum Γ n k g =ᶠ[𝓝 x] fun y => ∑ γ ∈ A, actPull n k (γ : RealGL) g y := by
    filter_upwards [hN] with y hy
    unfold actSum
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    exact hfin.mem_toFinset.mpr ⟨y, hy, actPull_ne_zero_mem g γ (hNp hy) hγ⟩
  have hd : ∀ γ ∈ A, DifferentiableAt ℝ (actPull n k (γ : RealGL) g) x := fun γ _ =>
    ((contDiffOn_actPull n k (γ : RealGL) hg.1.contDiffOn).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have hA : ∀ γ : Γ, actPull n (k + 1) (γ : RealGL) (extDeriv g) x ≠ 0 → γ ∈ A := fun γ hγ =>
    hfin.mem_toFinset.mpr ⟨x, mem_of_mem_nhds hN, by
      have := actPull_ne_zero_mem (extDeriv g) (γ : RealGL) hx hγ
      exact (tsupport_extDeriv_subset n k g) this⟩
  rw [hloc.extDeriv_eq, extDeriv_finset_sum A _ hd, actSum_eq_sum_of_superset A hA]
  exact Finset.sum_congr rfl fun γ _ => extDeriv_actPull n k (γ : RealGL) hg.1.contDiffOn hx

theorem Admissible.localAdjoint_actSum (h : Admissible Γ) {g : Coordinates → FormValue n (k + 1)}
    (hg : g ∈ Cc n (k + 1)) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    localAdjoint n k (actSum Γ n (k + 1) g) x = actSum Γ n k (localAdjoint n k g) x := by
  classical
  obtain ⟨N, hN, hNp, hfin⟩ := h.translates_locallyFinite hg.2.1 hg.2.2 x hx
  let A : Finset Γ := hfin.toFinset
  have hloc : actSum Γ n (k + 1) g =ᶠ[𝓝 x] fun y => ∑ γ ∈ A, actPull n (k + 1) (γ : RealGL) g y := by
    filter_upwards [hN] with y hy
    unfold actSum
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    exact hfin.mem_toFinset.mpr ⟨y, hy, actPull_ne_zero_mem g γ (hNp hy) hγ⟩
  have hA : ∀ γ : Γ, actPull n k (γ : RealGL) (localAdjoint n k g) x ≠ 0 → γ ∈ A := fun γ hγ =>
    hfin.mem_toFinset.mpr ⟨x, mem_of_mem_nhds hN, by
      have := actPull_ne_zero_mem (localAdjoint n k g) (γ : RealGL) hx hγ
      exact (tsupport_localAdjoint n k g) this⟩
  rw [localAdjoint_congr n k hloc, localAdjoint_finset_sum A _
    (fun γ _ => contDiffOn_actPull n (k + 1) (γ : RealGL) hg.1.contDiffOn) hx,
    actSum_eq_sum_of_superset A hA]
  exact Finset.sum_congr rfl fun γ _ =>
    localAdjoint_actPull n k (γ : RealGL) (h.det_sq γ) hg.1.contDiffOn hx

theorem Admissible.d_avgForm (h : Admissible Γ) {g : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) :
    CForm.d Γ n k (avgForm h g hg) = avgForm h (extDeriv g) (extDeriv_mem_Cc hg) := by
  apply CForm.ext
  intro x hx
  rw [CForm.d_apply _ hx, fn_avgForm h (extDeriv_mem_Cc hg) hx]
  have hloc : CForm.fn (avgForm h g hg) =ᶠ[𝓝 x] actSum Γ n k g := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy using fn_avgForm h hg hy
  rw [hloc.extDeriv_eq]
  exact h.extDeriv_actSum hg hx

theorem Admissible.delta_avgForm (h : Admissible Γ) {g : Coordinates → FormValue n (k + 1)}
    (hg : g ∈ Cc n (k + 1)) :
    CForm.delta Γ n k (avgForm h g hg) = avgForm h (localAdjoint n k g) (localAdjoint_mem_Cc hg) := by
  apply CForm.ext
  intro x hx
  rw [CForm.delta_apply h _ hx, fn_avgForm h (localAdjoint_mem_Cc hg) hx]
  have hloc : CForm.fn (avgForm h g hg) =ᶠ[𝓝 x] actSum Γ n (k + 1) g := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy using fn_avgForm h hg hy
  rw [localAdjoint_congr n k hloc]
  exact h.localAdjoint_actSum hg hx

theorem wL2_nonneg {g : Coordinates → FormValue n k}
    (hz : ∀ x ∉ positiveCoordinates, g x = 0) : 0 ≤ wL2 g := by
  refine integral_nonneg (fun x => ?_)
  by_cases hx : x ∈ positiveCoordinates
  · exact mul_nonneg (coordinateDensity_pos x hx).le (formPairing_nonneg n k x hx (g x))
  · have h0 := hz x hx
    have : weightedSquare n k g x = 0 := by
      unfold weightedSquare
      rw [h0, formPairing_zero_left, mul_zero]
    exact this.ge

theorem wL2_eq_localIntegral (g : Coordinates → FormValue n k) : wL2 g = localIntegral n k g g :=
  rfl

theorem Cc.zero_outside {g : Coordinates → FormValue n k} (hg : g ∈ Cc n k) :
    ∀ x ∉ positiveCoordinates, g x = 0 := fun _ hx =>
  image_eq_zero_of_notMem_tsupport (fun hh => hx (hg.2.2 hh))

theorem Admissible.normSq_avgForm_le_of_subset (h : Admissible Γ) {g : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) {K : Set Coordinates} (hK : IsCompact K) (hKp : K ⊆ positiveCoordinates)
    (hgK : tsupport g ⊆ K) :
    normSq (avgForm h g hg) ≤
      ((h.overlap_finite hK hKp).toFinset.card : ℝ) * wL2 g := by
  classical
  refine (h.normSq_avgForm_le hg).trans ?_
  have hcard : ((h.overlap_finite hg.2.1 hg.2.2).toFinset.card : ℝ) ≤
      ((h.overlap_finite hK hKp).toFinset.card : ℝ) := by
    have hsub : (h.overlap_finite hg.2.1 hg.2.2).toFinset ⊆ (h.overlap_finite hK hKp).toFinset := by
      intro γ hγ
      rw [Set.Finite.mem_toFinset] at hγ ⊢
      obtain ⟨y, hy, hγy⟩ := hγ
      exact ⟨y, hgK hy, hgK hγy⟩
    exact_mod_cast Finset.card_le_card hsub
  exact mul_le_mul_of_nonneg_right hcard (wL2_nonneg (Cc.zero_outside hg))

theorem aux_le_of_sq_le_mul {w P : ℝ} (hw : 0 ≤ w) (hP : 0 ≤ P) (h : w ^ 2 ≤ P * w) : w ≤ P := by
  by_cases h0 : w = 0
  · rw [h0]
    exact hP
  · have hpos : 0 < w := lt_of_le_of_ne hw (Ne.symm h0)
    have h2 : w * w ≤ P * w := by
      calc w * w = w ^ 2 := (sq w).symm
        _ ≤ P * w := h
    exact le_of_mul_le_mul_right h2 hpos

theorem aux_chain {w w2 N0 L S Nu U A : ℝ} (hw0 : 0 ≤ w) (hN0 : 0 ≤ N0) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hin : w ≤ U * A) (hUA : (U * A) ^ 2 = Nu * S) (hu : Nu ≤ N0 * w2) (hE : w2 ≤ L * w) :
    w ≤ N0 * L * S := by
  have h1 : w ^ 2 ≤ (U * A) ^ 2 := pow_le_pow_left₀ hw0 hin 2
  have h2 : Nu * S ≤ (N0 * w2) * S := mul_le_mul_of_nonneg_right hu hS
  have h3 : (N0 * w2) * S ≤ (N0 * (L * w)) * S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hN0) hS
  have h4 : w ^ 2 ≤ (N0 * L * S) * w := by
    calc w ^ 2 ≤ (U * A) ^ 2 := h1
      _ = Nu * S := hUA
      _ ≤ (N0 * w2) * S := h2
      _ ≤ (N0 * (L * w)) * S := h3
      _ = (N0 * L * S) * w := by ring
  exact aux_le_of_sq_le_mul hw0 (mul_nonneg (mul_nonneg hN0 hL) hS) h4

theorem formPairing_cut_self (n k : ℕ) (x : Coordinates) (t : ℝ) (a : FormValue n k) :
    formPairing n k x (t • a) (t • a) = t * (t * formPairing n k x a a) :=
  (formPairing_smul_left n k x t a (t • a)).trans
    (congrArg (fun r : ℝ => t * r) (formPairing_smul_right n k x t a a))

theorem formPairing_cut_cut (n k : ℕ) (x : Coordinates) (t : ℝ) (a : FormValue n k) :
    formPairing n k x (t • (t • a)) a = t * (t * formPairing n k x a a) :=
  (formPairing_smul_left n k x t (t • a) a).trans
    (congrArg (fun r : ℝ => t * r) (formPairing_smul_left n k x t a a))

theorem cut_mem_Cc {ψ : Coordinates → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ positiveCoordinates) {f : Coordinates → FormValue n k}
    (hf : ContDiffOn ℝ ∞ f positiveCoordinates) : (fun y => ψ y • f y) ∈ Cc n k :=
  ⟨contDiff_cut hψ hsψ hf, hasCompactSupport_cut hcψ f, (tsupport_cut_subset ψ f).trans hsψ⟩

theorem wL2_cut_eq_l2Form (h : Admissible Γ) {ψ : Coordinates → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ positiveCoordinates) (a : CForm Γ n k) :
    wL2 (fun y => ψ y • CForm.fn a y) = l2Form Γ n k (avgForm h
      (fun y => ψ y • (ψ y • CForm.fn a y))
      (cut_mem_Cc hψ hcψ hsψ (cut_mem_Cc hψ hcψ hsψ (CForm.smooth a)).1.contDiffOn)) a := by
  have hg1 := cut_mem_Cc hψ hcψ hsψ (CForm.smooth a)
  rw [h.l2Form_avg, wL2_eq_localIntegral,
    localIntegral_eq_setIntegral n k _ _ (Cc.zero_outside hg1)]
  refine setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet (fun x _ => ?_)
  rw [formPairing_cut_self, formPairing_cut_cut]

theorem wL2_cut_cut_le {ψ : Coordinates → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ positiveCoordinates) {Λ : ℝ}
    (hΛ : ∀ y, |ψ y| ≤ Λ) {f : Coordinates → FormValue n k}
    (hf : ContDiffOn ℝ ∞ f positiveCoordinates) :
    wL2 (fun y => ψ y • (ψ y • f y)) ≤ Λ ^ 2 * wL2 (fun y => ψ y • f y) := by
  have hg1 := cut_mem_Cc hψ hcψ hsψ hf
  have hg2 := cut_mem_Cc hψ hcψ hsψ hg1.1.contDiffOn
  unfold wL2
  rw [← integral_const_mul]
  refine integral_mono (integrable_weightedSquare n k _ hg2.1.contDiffOn hg2.2.1 hg2.2.2)
    ((integrable_weightedSquare n k _ hg1.1.contDiffOn hg1.2.1 hg1.2.2).const_mul _) (fun x => ?_)
  by_cases hx : x ∈ positiveCoordinates
  · have hρ := (coordinateDensity_pos x hx).le
    have hp := formPairing_nonneg n k x hx (f x)
    have hψ2 : ψ x ^ 2 ≤ Λ ^ 2 := sq_le_sq' (abs_le.mp (hΛ x)).1 (abs_le.mp (hΛ x)).2
    have hm := mul_nonneg hρ hp
    have e1 : weightedSquare n k (fun y => ψ y • (ψ y • f y)) x =
        coordinateDensity x * (ψ x * (ψ x * (ψ x * (ψ x * formPairing n k x (f x) (f x))))) :=
      congrArg (fun r : ℝ => coordinateDensity x * r)
        ((formPairing_cut_self n k x (ψ x) (ψ x • f x)).trans
          (congrArg (fun r : ℝ => ψ x * (ψ x * r)) (formPairing_cut_self n k x (ψ x) (f x))))
    have e2 : weightedSquare n k (fun y => ψ y • f y) x =
        coordinateDensity x * (ψ x * (ψ x * formPairing n k x (f x) (f x))) :=
      congrArg (fun r : ℝ => coordinateDensity x * r) (formPairing_cut_self n k x (ψ x) (f x))
    rw [e1, e2]
    nlinarith [mul_nonneg hm (sq_nonneg (ψ x)),
      mul_le_mul_of_nonneg_left hψ2 (mul_nonneg hm (sq_nonneg (ψ x)))]
  · have e1 : ψ x • f x = 0 := Cc.zero_outside hg1 x hx
    have e2 : ψ x • (ψ x • f x) = 0 := Cc.zero_outside hg2 x hx
    have z1 : weightedSquare n k (fun y => ψ y • (ψ y • f y)) x = 0 := by
      unfold weightedSquare
      rw [show (fun y => ψ y • (ψ y • f y)) x = 0 from e2, formPairing_zero_left, mul_zero]
    have z2 : weightedSquare n k (fun y => ψ y • f y) x = 0 := by
      unfold weightedSquare
      rw [show (fun y => ψ y • f y) x = 0 from e1, formPairing_zero_left, mul_zero]
    rw [z1, z2, mul_zero]

variable [hΓ : Fact (Admissible Γ)]

/-- The metric-density mass of a compactly supported cutoff of an equivariant form is controlled by
its `L²` norm on the orbit space. -/
theorem wL2_cut_le {ψ : Coordinates → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ positiveCoordinates) {Λ : ℝ} (hΛ : ∀ y, |ψ y| ≤ Λ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ a : CForm Γ n k, wL2 (fun y => ψ y • CForm.fn a y) ≤ N * normSq a := by
  classical
  have h := hΓ.out
  have hK : IsCompact (tsupport ψ) := hcψ.isCompact
  refine ⟨((h.overlap_finite hK hsψ).toFinset.card : ℝ) * Λ ^ 2,
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg Λ), fun a => ?_⟩
  have hg1 := cut_mem_Cc hψ hcψ hsψ (CForm.smooth a)
  have hg2 := cut_mem_Cc hψ hcψ hsψ hg1.1.contDiffOn
  have E1 := wL2_cut_eq_l2Form h hψ hcψ hsψ a
  have E4 := wL2_cut_cut_le hψ hcψ hsψ hΛ (CForm.smooth a)
  have hw0 : 0 ≤ wL2 (fun y => ψ y • CForm.fn a y) := wL2_nonneg (Cc.zero_outside hg1)
  have hu := h.normSq_avgForm_le_of_subset hg2 hK hsψ (tsupport_cut_subset ψ _)
  have hin : wL2 (fun y => ψ y • CForm.fn a y) ≤
      ‖incl Γ n k (avgForm h _ hg2)‖ * ‖incl Γ n k a‖ :=
    (E1.trans (inner_incl Γ n k _ a).symm).trans_le (real_inner_le_norm _ _)
  have hUA : (‖incl Γ n k (avgForm h _ hg2)‖ * ‖incl Γ n k a‖) ^ 2 =
      normSq (avgForm h _ hg2) * normSq a :=
    (mul_pow _ _ 2).trans (congrArg₂ (· * ·) (norm_incl_sq Γ n k _) (norm_incl_sq Γ n k a))
  exact aux_chain hw0 (Nat.cast_nonneg _) (sq_nonneg Λ) (normSq_nonneg a) hin hUA hu E4

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
