module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.PrimGauge

@[expose] public section


/-! # General coercivity, Tier B (phase F): transport of test forms and smooth forms by the group

Open images of boxes, restriction of the pullback to test forms with prescribed support, and the
local version of the smoothness of the normalized pullback.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.PolynomialFormWeakSmooth TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.CompactCoordinateIntegration
  TernaryPoly.SmoothCoveringDeRham TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
  TernaryPoly.SmoothLocalDeRham
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n k : ℕ} {Γ : Subgroup RealGL}

/-- The image of an open subset of the positive coordinates under the coordinate action. -/
def imgOpen (γ : RealGL) (U : TopologicalSpace.Opens Coordinates)
    (hU : (U : Set Coordinates) ⊆ positiveCoordinates) : TopologicalSpace.Opens Coordinates :=
  ⟨coordinateAction γ '' U, (actionCoordinates γ).isOpen_image_of_subset_source U.isOpen hU⟩

theorem coe_imgOpen (γ : RealGL) (U : TopologicalSpace.Opens Coordinates)
    (hU : (U : Set Coordinates) ⊆ positiveCoordinates) :
    ((imgOpen γ U hU : TopologicalSpace.Opens Coordinates) : Set Coordinates) =
      coordinateAction γ '' U := rfl

theorem imgOpen_subset_positive (γ : RealGL) (U : TopologicalSpace.Opens Coordinates)
    (hU : (U : Set Coordinates) ⊆ positiveCoordinates) :
    ((imgOpen γ U hU : TopologicalSpace.Opens Coordinates) : Set Coordinates) ⊆ positiveCoordinates := by
  rintro _ ⟨x, hx, rfl⟩
  exact coordinateAction_mem γ x (hU hx)

theorem coordinateAction_inv_image (γ : RealGL) {U : Set Coordinates} (hU : U ⊆ positiveCoordinates) :
    coordinateAction γ⁻¹ '' (coordinateAction γ '' U) = U := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rwa [coordinateAction_inv_apply γ (hU hx)]
  · intro hy
    exact ⟨coordinateAction γ y, ⟨y, hy, rfl⟩, coordinateAction_inv_apply γ (hU hy)⟩

/-- The pullback restricted to test forms supported in the image of `U`. -/
def pullIn (γ : RealGL) (U : TopologicalSpace.Opens Coordinates)
    (hU : (U : Set Coordinates) ⊆ positiveCoordinates) :
    CcIn n k (coordinateAction γ '' U) →ₗ[ℝ] CcIn n k (U : Set Coordinates) :=
  LinearMap.codRestrict (CcIn n k (U : Set Coordinates)) ((pullCc γ).comp (CcIn n k _).subtype)
    (fun f => by
      change tsupport (actPull n k γ f.1.1) ⊆ U
      refine (tsupport_actPull n k γ f.1.1 f.1.2.2.1 f.1.2.2.2).trans ?_
      refine (image_mono f.2).trans ?_
      rw [coordinateAction_inv_image γ hU])

theorem pullIn_coe (γ : RealGL) (U : TopologicalSpace.Opens Coordinates)
    (hU : (U : Set Coordinates) ⊆ positiveCoordinates)
    (f : CcIn n k (coordinateAction γ '' U)) :
    ((pullIn γ U hU f : CcIn n k (U : Set Coordinates)).1 : Cc n k) = pullCc γ f.1 := rfl

/-- Smoothness of the normalized pullback of a form that is smooth only on a subset. -/
theorem contDiffOn_actPull_local (γ : RealGL) {s t : Set Coordinates} (hs : IsOpen s)
    (hsp : s ⊆ positiveCoordinates) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w t) (hmap : MapsTo (coordinateAction γ) s t) :
    ContDiffOn ℝ ∞ (actPull n k γ w) s := by
  have h := coefficientRaw_smooth (realCoefficientMap n γ⁻¹)
    (pullRaw_smooth hs ((contDiffOn_coordinateAction γ).mono hsp) hw hmap)
  exact h.congr (fun x hx => actPull_apply n k γ w (hsp hx))

/-- Local primitive data on an open set `B`: a smooth form `v` and a functional `S` on zero-forms
with `T = ⟨v, ·⟩ + S ∘ δ` on test one-forms supported in `B`. -/
structure LocalPrim (B : TopologicalSpace.Opens Coordinates) (T : Cc n 1 →ₗ[ℝ] ℝ) where
  v : Coordinates → FormValue n 1
  hv : ContDiffOn ℝ ∞ v B
  S : CcIn n 0 (B : Set Coordinates) →ₗ[ℝ] ℝ
  prim : ∀ g : CcIn n 1 (B : Set Coordinates),
    T g.1 = pairIn B v hv.continuousOn g + S (deltaIn n 0 (B : Set Coordinates) g)

theorem pairIn_sub (Ω : TopologicalSpace.Opens Coordinates) {a b : Coordinates → FormValue n k}
    (ha : ContinuousOn a Ω) (hb : ContinuousOn b Ω) (g : CcIn n k (Ω : Set Coordinates)) :
    pairIn Ω (fun x => a x - b x) (ha.sub hb) g = pairIn Ω a ha g - pairIn Ω b hb g := by
  rw [pairIn_apply, pairIn_apply, pairIn_apply, ← integral_sub (integrable_pairing Ω a ha g)
    (integrable_pairing Ω b hb g)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have h : formPairing n k x (a x - b x) (g.1.1 x) =
      formPairing n k x (a x) (g.1.1 x) - formPairing n k x (b x) (g.1.1 x) := by
    have e : a x - b x = a x + (-1 : ℝ) • b x := by
      exact ContinuousAlternatingMap.ext fun w => by simp [sub_eq_add_neg]
    rw [e, formPairing_add_left, formPairing_smul_left]
    ring
  show coordinateDensity x * formPairing n k x (a x - b x) (g.1.1 x) = _
  rw [h]
  ring

/-! ### The transported cutoff of a pair `p = (γ, i)` -/

section Pair

variable (D : BoxData Γ)

/-- `u_p = ρ_i ∘ γ⁻¹`, extended by zero. -/
def ucut (p : Γ × D.ι) : Coordinates → ℝ := cutAct ((p.1 : RealGL)⁻¹) (D.ρ p.2)

theorem tsupport_ρ_pos (i : D.ι) : tsupport (D.ρ i) ⊆ positiveCoordinates :=
  (D.tsupport_subset i).trans (D.box_pos i)

theorem ucut_smooth (p : Γ × D.ι) : ContDiff ℝ ∞ (ucut D p) :=
  contDiff_cutAct _ (D.smooth p.2) (D.compact p.2) (tsupport_ρ_pos D p.2)

theorem ucut_compact (p : Γ × D.ι) : HasCompactSupport (ucut D p) :=
  hasCompactSupport_cutAct _ (D.compact p.2) (tsupport_ρ_pos D p.2)

theorem tsupport_ucut (p : Γ × D.ι) :
    tsupport (ucut D p) ⊆ coordinateAction (p.1 : RealGL) '' tsupport (D.ρ p.2) := by
  have := tsupport_cutAct_subset ((p.1 : RealGL)⁻¹) (D.compact p.2) (tsupport_ρ_pos D p.2)
  rw [inv_inv] at this
  exact this

theorem tsupport_ucut_subset_img (p : Γ × D.ι) :
    tsupport (ucut D p) ⊆ coordinateAction (p.1 : RealGL) '' (D.box p.2 : Set Coordinates) :=
  (tsupport_ucut D p).trans (image_mono (D.tsupport_subset p.2))

variable (B : TopologicalSpace.Opens Coordinates)

/-- `g ↦ [d, u_p] g`, a test zero-form supported in `B`. -/
def qB (p : Γ × D.ι) : CcIn n 1 (B : Set Coordinates) →ₗ[ℝ] CcIn n 0 (B : Set Coordinates) :=
  LinearMap.codRestrict (CcIn n 0 (B : Set Coordinates))
    ((commCc (ucut D p) (ucut_smooth D p)).comp (CcIn n 1 (B : Set Coordinates)).subtype)
    (fun g => (tsupport_commCc _ _ g.1).trans (inter_subset_right.trans g.2))

/-- The pullback of `[d, u_p] g` by `γ`, a test zero-form supported in the box `B_i`. -/
def qI (p : Γ × D.ι) : CcIn n 1 (B : Set Coordinates) →ₗ[ℝ] CcIn n 0 (D.box p.2 : Set Coordinates) :=
  LinearMap.codRestrict (CcIn n 0 (D.box p.2 : Set Coordinates))
    ((pullCc (p.1 : RealGL)).comp
      ((commCc (ucut D p) (ucut_smooth D p)).comp (CcIn n 1 (B : Set Coordinates)).subtype))
    (fun g => by
      change tsupport (actPull n 0 (p.1 : RealGL) (commCc (ucut D p) (ucut_smooth D p) g.1).1) ⊆
        (D.box p.2 : Set Coordinates)
      have hq := (commCc (ucut D p) (ucut_smooth D p) g.1).2
      refine (tsupport_actPull n 0 _ _ hq.2.1 hq.2.2).trans ?_
      refine (image_mono ((tsupport_commCc _ _ g.1).trans inter_subset_left)).trans ?_
      refine (image_mono (tsupport_ucut D p)).trans ?_
      rw [coordinateAction_inv_image (p.1 : RealGL) (tsupport_ρ_pos D p.2)]
      exact D.tsupport_subset p.2)

theorem qB_coe (p : Γ × D.ι) (g : CcIn n 1 (B : Set Coordinates)) :
    ((qB D B p g : CcIn n 0 (B : Set Coordinates)).1 : Cc n 0) =
      commCc (ucut D p) (ucut_smooth D p) g.1 := rfl

theorem qI_coe (p : Γ × D.ι) (g : CcIn n 1 (B : Set Coordinates)) :
    ((qI D B p g : CcIn n 0 (D.box p.2 : Set Coordinates)).1 : Cc n 0) =
      pullCc (p.1 : RealGL) (commCc (ucut D p) (ucut_smooth D p) g.1) := rfl

/-- The overlap `B ∩ γ B_i` of a box with a translate of the `i`-th box. -/
def Vp (p : Γ × D.ι) : TopologicalSpace.Opens Coordinates :=
  B ⊓ imgOpen (p.1 : RealGL) (D.box p.2) (D.box_pos p.2)

theorem Vp_subset_B (p : Γ × D.ι) : (Vp D B p : Set Coordinates) ⊆ B := inter_subset_left

theorem Vp_subset_img (p : Γ × D.ι) :
    (Vp D B p : Set Coordinates) ⊆ coordinateAction (p.1 : RealGL) '' (D.box p.2 : Set Coordinates) :=
  inter_subset_right

/-- The functional `S_B - S_i ∘ γ^*` on zero-forms supported in the overlap. -/
def Apair (T : Cc n 1 →ₗ[ℝ] ℝ) (p : Γ × D.ι) (GB : LocalPrim B T) (Gi : LocalPrim (D.box p.2) T) :
    CcIn n 0 (Vp D B p : Set Coordinates) →ₗ[ℝ] ℝ :=
  GB.S.comp (inclIn (Vp_subset_B D B p)) -
    Gi.S.comp ((pullIn (p.1 : RealGL) (D.box p.2) (D.box_pos p.2)).comp
      (inclIn (Vp_subset_img D B p)))

theorem per_p_aux (h : Admissible Γ) (T : Cc n 1 →ₗ[ℝ] ℝ)
    (hinv : ∀ (δ : Γ) (g : Cc n 1), T (pullCc (δ : RealGL) g) = T g) (p : Γ × D.ι)
    (hB : (B : Set Coordinates) ⊆ positiveCoordinates) (GB : LocalPrim B T)
    (Gi : LocalPrim (D.box p.2) T) :
    ∃ (f : Coordinates → FormValue n 0) (hf : ContDiffOn ℝ ∞ f (Vp D B p)),
      ∀ g : CcIn n 0 (Vp D B p : Set Coordinates), Apair D B T p GB Gi g = pairIn _ f hf.continuousOn g := by
  have hγ : (p.1 : RealGL).val.det ^ 2 = 1 := h.det_sq p.1
  have hVpos : (Vp D B p : Set Coordinates) ⊆ positiveCoordinates := (Vp_subset_B D B p).trans hB
  let v0 : Coordinates → FormValue n 1 := (D.box p.2 : Set Coordinates).indicator Gi.v
  have hv0 : ContDiffOn ℝ ∞ v0 (D.box p.2) := Gi.hv.congr (fun x hx => indicator_of_mem hx _)
  have hv00 : ∀ x ∉ positiveCoordinates, v0 x = 0 := fun x hx =>
    indicator_of_notMem (fun hh => hx (D.box_pos p.2 hh)) _
  have ha : ContDiffOn ℝ ∞ (actPull n 1 ((p.1 : RealGL)⁻¹) v0) (Vp D B p) := by
    refine contDiffOn_actPull_local ((p.1 : RealGL)⁻¹) (Vp D B p).isOpen hVpos hv0 ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Vp_subset_img D B p hx
    rwa [coordinateAction_inv_apply _ (D.box_pos p.2 hy)]
  have hb : ContDiffOn ℝ ∞ GB.v (Vp D B p) := GB.hv.mono (Vp_subset_B D B p)
  have hθ : ContDiffOn ℝ ∞ (fun x => actPull n 1 ((p.1 : RealGL)⁻¹) v0 x - GB.v x) (Vp D B p) :=
    ha.sub hb
  have hA : ∀ k : CcIn n 1 (Vp D B p : Set Coordinates),
      Apair D B T p GB Gi (deltaIn n 0 (Vp D B p : Set Coordinates) k) =
        pairIn (Vp D B p) _ hθ.continuousOn k := by
    intro k
    have e1 : GB.S (inclIn (Vp_subset_B D B p) (deltaIn n 0 (Vp D B p : Set Coordinates) k)) =
        T k.1 - pairIn B GB.v GB.hv.continuousOn (inclIn (Vp_subset_B D B p) k) := by
      have h0 := GB.prim (inclIn (Vp_subset_B D B p) k)
      have h2 : GB.S (inclIn (Vp_subset_B D B p) (deltaIn n 0 (Vp D B p : Set Coordinates) k)) =
          GB.S (deltaIn n 0 (B : Set Coordinates) (inclIn (Vp_subset_B D B p) k)) :=
        (congrArg GB.S (deltaIn_inclIn (Vp_subset_B D B p) k)).symm
      exact h2.trans (eq_sub_of_add_eq' h0.symm)
    let kI : CcIn n 1 (D.box p.2 : Set Coordinates) :=
      pullIn (p.1 : RealGL) (D.box p.2) (D.box_pos p.2) (inclIn (Vp_subset_img D B p) k)
    have hpd : pullIn (p.1 : RealGL) (D.box p.2) (D.box_pos p.2)
        (inclIn (Vp_subset_img D B p) (deltaIn n 0 (Vp D B p : Set Coordinates) k)) =
        deltaIn n 0 (D.box p.2 : Set Coordinates) kI := by
      apply Subtype.ext
      exact (deltaCc_pullCc (p.1 : RealGL) hγ k.1).symm
    have hTkI : T kI.1 = T k.1 := hinv p.1 k.1
    have hI : pairIn (D.box p.2) Gi.v Gi.hv.continuousOn kI =
        ∫ x, coordinateDensity x * formPairing n 1 x
          (actPull n 1 ((p.1 : RealGL)⁻¹) v0 x) (k.1.1 x) := by
      have h1 : pairIn (D.box p.2) Gi.v Gi.hv.continuousOn kI =
          localIntegral n 1 v0 (actPull n 1 (p.1 : RealGL) k.1.1) := by
        rw [pairIn_apply]
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        by_cases hx : x ∈ tsupport kI.1.1
        · change coordinateDensity x * formPairing n 1 x (Gi.v x) (kI.1.1 x) =
            coordinateDensity x * formPairing n 1 x (v0 x) (actPull n 1 (p.1 : RealGL) k.1.1 x)
          rw [show v0 x = Gi.v x from indicator_of_mem (kI.2 hx) _]
          rfl
        · have h0 : kI.1.1 x = 0 := image_eq_zero_of_notMem_tsupport hx
          change coordinateDensity x * formPairing n 1 x (Gi.v x) (kI.1.1 x) =
            coordinateDensity x * formPairing n 1 x (v0 x) (actPull n 1 (p.1 : RealGL) k.1.1 x)
          have h0' : actPull n 1 (p.1 : RealGL) k.1.1 x = 0 := h0
          rw [h0']
          rw [h0]
          simp
      rw [h1, localIntegral_actPull_right n 1 _ hγ v0 k.1.1 hv00]
      rfl
    have e2 : Gi.S (deltaIn n 0 (D.box p.2 : Set Coordinates) kI) =
        T k.1 - ∫ x, coordinateDensity x * formPairing n 1 x
          (actPull n 1 ((p.1 : RealGL)⁻¹) v0 x) (k.1.1 x) := by
      have h0 := Gi.prim kI
      exact (eq_sub_of_add_eq' h0.symm).trans (congrArg₂ (fun a b : ℝ => a - b) hTkI hI)
    have e3 : pairIn (Vp D B p) _ hθ.continuousOn k =
        (∫ x, coordinateDensity x * formPairing n 1 x
          (actPull n 1 ((p.1 : RealGL)⁻¹) v0 x) (k.1.1 x)) -
        pairIn B GB.v GB.hv.continuousOn (inclIn (Vp_subset_B D B p) k) := by
      exact (pairIn_sub (Vp D B p) ha.continuousOn hb.continuousOn k).trans rfl
    have e4 : Apair D B T p GB Gi (deltaIn n 0 (Vp D B p : Set Coordinates) k) =
        GB.S (inclIn (Vp_subset_B D B p) (deltaIn n 0 (Vp D B p : Set Coordinates) k)) -
          Gi.S (pullIn (p.1 : RealGL) (D.box p.2) (D.box_pos p.2)
            (inclIn (Vp_subset_img D B p) (deltaIn n 0 (Vp D B p : Set Coordinates) k))) := rfl
    exact e4.trans ((congrArg₂ (fun a b : ℝ => a - b) e1 ((congrArg Gi.S hpd).trans e2)).trans
      ((sub_sub_sub_cancel_left _ _ _).trans e3.symm))
  obtain ⟨f, hf, hrep⟩ := weyl_open (Vp D B p) hVpos (Apair D B T p GB Gi) _ hθ hA
  exact ⟨f, hf, hrep⟩

theorem formPairing_zero_left' (n k : ℕ) (x : Coordinates) (b : FormValue n k) :
    formPairing n k x 0 b = 0 := by
  have h := formPairing_smul_left n k x 0 (0 : FormValue n k) b
  have e : (0 : ℝ) • (0 : FormValue n k) = 0 := ContinuousAlternatingMap.ext fun w => by simp
  rw [e] at h
  linarith

theorem per_p (h : Admissible Γ) (T : Cc n 1 →ₗ[ℝ] ℝ)
    (hinv : ∀ (δ : Γ) (g : Cc n 1), T (pullCc (δ : RealGL) g) = T g) (p : Γ × D.ι)
    (hB : (B : Set Coordinates) ⊆ positiveCoordinates) (GB : LocalPrim B T)
    (Gi : LocalPrim (D.box p.2) T) :
    ∃ (η : Coordinates → FormValue n 1) (hη : ContDiffOn ℝ ∞ η B),
      ∀ g : CcIn n 1 (B : Set Coordinates),
        GB.S (qB D B p g) - Gi.S (qI D B p g) = pairIn B η hη.continuousOn g := by
  have hex := per_p_aux D B h T hinv p hB GB Gi
  obtain ⟨fp, hfp, hrep⟩ := hex
  let u : Coordinates → ℝ := ucut D p
  have hu : ContDiff ℝ ∞ u := ucut_smooth D p
  let Λ : CcIn n 1 (B : Set Coordinates) →ₗ[ℝ] ℝ := GB.S.comp (qB D B p) - Gi.S.comp (qI D B p)
  have key : ∀ x ∈ (B : Set Coordinates), ∃ (U : TopologicalSpace.Opens Coordinates)
      (hU : (U : Set Coordinates) ⊆ B) (_ : x ∈ (U : Set Coordinates))
      (f : Coordinates → FormValue n 1) (hf : ContDiffOn ℝ ∞ f U),
      ∀ g : CcIn n 1 (U : Set Coordinates), Λ (inclIn hU g) = pairIn U f hf.continuousOn g := by
    intro x hxB
    by_cases hx : x ∈ coordinateAction (p.1 : RealGL) '' (D.box p.2 : Set Coordinates)
    · refine ⟨Vp D B p, Vp_subset_B D B p, ⟨hxB, hx⟩, localDifferentialSymbol n 0 u fp,
        contDiffOn_localDifferentialSymbol u hu hfp, fun g => ?_⟩
      let q : CcIn n 0 (Vp D B p : Set Coordinates) :=
        ⟨commCc u hu g.1, (tsupport_commCc u hu g.1).trans (inter_subset_right.trans g.2)⟩
      have eΛ : Λ (inclIn (Vp_subset_B D B p) g) = Apair D B T p GB Gi q := rfl
      refine (eΛ.trans (hrep q)).trans ((pairIn_apply _ _ _ _).trans (Eq.trans ?_ (pairIn_apply _ _ _ _).symm))
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      by_cases hy : y ∈ positiveCoordinates
      · exact pair_commCc u hu fp g.1 hy
      · have h1 : (commCc u hu g.1).1 y = 0 := Cc.zero_outside (commCc u hu g.1).2 y hy
        have h2 : g.1.1 y = 0 := Cc.zero_outside g.1.2 y hy
        change coordinateDensity y * formPairing n 0 y (fp y) ((commCc u hu g.1).1 y) =
          coordinateDensity y * formPairing n 1 y (localDifferentialSymbol n 0 u fp y) (g.1.1 y)
        rw [h1, h2]
        simp
    · let U : TopologicalSpace.Opens Coordinates := B ⊓ ⟨(tsupport u)ᶜ, (isClosed_tsupport u).isOpen_compl⟩
      have hxu : x ∉ tsupport u := fun hh => hx (tsupport_ucut_subset_img D p hh)
      refine ⟨U, inf_le_left, ⟨hxB, hxu⟩, fun _ => 0, contDiffOn_const, fun g => ?_⟩
      let gB : CcIn n 1 (B : Set Coordinates) := inclIn (inf_le_left : (U : Set Coordinates) ⊆ B) g
      have hq0 : commCc u hu gB.1 = 0 := by
        apply Subtype.ext
        funext y
        have hsub := tsupport_commCc u hu gB.1
        have hy : y ∉ tsupport (commCc u hu gB.1).1 := fun hy =>
          (g.2 (hsub hy).2).2 (hsub hy).1
        exact image_eq_zero_of_notMem_tsupport hy
      have eB : qB D B p gB = 0 := Subtype.ext hq0
      have eI : qI D B p gB = 0 := Subtype.ext (by
        change pullCc (p.1 : RealGL) (commCc u hu gB.1) = 0
        exact (congrArg (pullCc (p.1 : RealGL)) hq0).trans (pullCc (p.1 : RealGL)).map_zero)
      have eΛ : Λ gB = 0 := by
        change GB.S (qB D B p gB) - Gi.S (qI D B p gB) = 0
        exact (congrArg₂ (fun a b : ℝ => a - b) ((congrArg GB.S eB).trans GB.S.map_zero)
          ((congrArg Gi.S eI).trans Gi.S.map_zero)).trans (sub_zero 0)
      have hz : (fun x => coordinateDensity x * formPairing n 1 x ((fun _ => (0 : FormValue n 1)) x)
          (g.1.1 x)) = fun _ => (0 : ℝ) := funext fun x => by
        show coordinateDensity x * formPairing n 1 x 0 (g.1.1 x) = 0
        rw [formPairing_zero_left', mul_zero]
      refine eΛ.trans (Eq.trans ?_ (pairIn_apply _ _ _ _).symm)
      rw [hz, integral_zero]
  have hex2 := exists_smooth_of_local B hB Λ key
  obtain ⟨η, hη, hrepη⟩ := hex2
  exact ⟨η, hη, hrepη⟩

end Pair

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
