module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Average
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Forms.Pairing
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Measure.Unfolding

@[expose] public section


/-! # General coercivity, Tier B: the average as a linear map and the unfolding identity

`avg h : Cc n k →ₗ[ℝ] CForm Γ n k` is the push-forward `g ↦ ∑_γ γ*g`.  Its `L²` pairing against any
equivariant form `b` is the plain integral of the pointwise metric over the positive coordinates
(`l2Form_avg`), and its squared norm is bounded by the overlap number of the support times the
plain `L²` mass of `g` (`normSq_avg_le`).

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.PolynomialFormCoordinates
open MeasureTheory Set Filter Topology
open scoped ContDiff

variable {Γ : Subgroup RealGL} {n k : ℕ}

/-! ### The average as an element of `CForm` -/

theorem actSum_eq_sum_of_superset {g : Coordinates → FormValue n k}
    {x : Coordinates} (A : Finset Γ)
    (hA : ∀ γ : Γ, actPull n k (γ : RealGL) g x ≠ 0 → γ ∈ A) :
    actSum Γ n k g x = ∑ γ ∈ A, actPull n k (γ : RealGL) g x := by
  unfold actSum
  exact finsum_eq_sum_of_support_subset _ (fun γ hγ => hA γ hγ)

theorem Admissible.actSum_add (h : Admissible Γ) {g g' : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) (hg' : g' ∈ Cc n k) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    actSum Γ n k (g + g') x = actSum Γ n k g x + actSum Γ n k g' x := by
  classical
  let A : Finset Γ := (h.actSum_support_finite hg hx).toFinset ∪ (h.actSum_support_finite hg' hx).toFinset
  have hA : ∀ γ : Γ, actPull n k (γ : RealGL) g x ≠ 0 → γ ∈ A := fun γ hγ =>
    Finset.mem_union_left _ ((h.actSum_support_finite hg hx).mem_toFinset.mpr hγ)
  have hA' : ∀ γ : Γ, actPull n k (γ : RealGL) g' x ≠ 0 → γ ∈ A := fun γ hγ =>
    Finset.mem_union_right _ ((h.actSum_support_finite hg' hx).mem_toFinset.mpr hγ)
  have hA'' : ∀ γ : Γ, actPull n k (γ : RealGL) (g + g') x ≠ 0 → γ ∈ A := by
    intro γ hγ
    by_contra hnot
    apply hγ
    have h1 : actPull n k (γ : RealGL) g x = 0 := by
      by_contra h1
      exact hnot (hA γ h1)
    have h2 : actPull n k (γ : RealGL) g' x = 0 := by
      by_contra h2
      exact hnot (hA' γ h2)
    rw [actPull_add n k _ g g' hx, h1, h2, add_zero]
  rw [actSum_eq_sum_of_superset A hA'', actSum_eq_sum_of_superset A hA,
    actSum_eq_sum_of_superset A hA', ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun γ _ => actPull_add n k _ g g' hx

theorem Admissible.actSum_smul (h : Admissible Γ) {g : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) (c : ℝ) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    actSum Γ n k (c • g) x = c • actSum Γ n k g x := by
  classical
  let A : Finset Γ := (h.actSum_support_finite hg hx).toFinset
  have hA : ∀ γ : Γ, actPull n k (γ : RealGL) g x ≠ 0 → γ ∈ A := fun γ hγ =>
    (h.actSum_support_finite hg hx).mem_toFinset.mpr hγ
  have hA' : ∀ γ : Γ, actPull n k (γ : RealGL) (c • g) x ≠ 0 → γ ∈ A := by
    intro γ hγ
    rw [actPull_smul n k _ c g hx] at hγ
    exact hA γ (fun h0 => hγ (by rw [h0]; exact smul_zero (A := FormValue n k) c))
  rw [actSum_eq_sum_of_superset A hA', actSum_eq_sum_of_superset A hA]
  refine Eq.trans (Finset.sum_congr rfl fun γ _ => actPull_smul n k _ c g hx) ?_
  exact (Finset.smul_sum (r := c) (s := A) (f := fun γ : Γ => actPull n k (γ : RealGL) g x)).symm

theorem Admissible.projSupport_actSum_subset (h : Admissible Γ) {g : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) :
    closure (coordProj Γ '' Function.support (actSum Γ n k g)) ⊆ coordProj Γ '' tsupport g := by
  have hcomp : IsCompact (coordProj Γ '' tsupport g) :=
    hg.2.1.image_of_continuousOn (continuousOn_coordProj.mono hg.2.2)
  have : T2Space (OrbitSpace Γ) := h.t2
  apply closure_minimal _ hcomp.isClosed
  rintro _ ⟨x, hx, rfl⟩
  have hxp : x ∈ positiveCoordinates := by
    by_contra hn
    exact hx (actSum_of_notMem g hn)
  have hne : ∃ γ : Γ, actPull n k (γ : RealGL) g x ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx
    unfold actSum
    simp [hall]
  obtain ⟨γ, hγ⟩ := hne
  exact ⟨coordinateAction (γ : RealGL) x, actPull_ne_zero_mem g γ hxp hγ, coordProj_action γ hxp⟩

/-- The average of a compactly supported smooth form: a compactly supported equivariant form. -/
def avgForm (h : Admissible Γ) (g : Coordinates → FormValue n k) (hg : g ∈ Cc n k) :
    CForm Γ n k :=
  ⟨restrictForm positiveCoordinates (actSum Γ n k g) (h.contDiffOn_actSum hg), by
    have hres : ∀ y ∈ positiveCoordinates,
        (restrictForm positiveCoordinates (actSum Γ n k g) (h.contDiffOn_actSum hg) :
          Coordinates → FormValue n k) y = actSum Γ n k g y := fun y hy =>
      restrictForm_apply _ _ hy
    refine ⟨?_, ?_⟩
    · rw [isEquivariant_iff]
      intro γ x hx
      apply equivariantAt_of_actPull_eq
      · exact hx
      · have h1 := h.actPull_actSum hg γ hx
        rw [actPull_apply n k _ _ hx, hres _ (coordinateAction_mem _ x hx), hres x hx]
        rw [actPull_apply n k _ _ hx] at h1
        exact h1
    · have hsub : projSupport Γ (restrictForm positiveCoordinates (actSum Γ n k g)
          (h.contDiffOn_actSum hg) : Coordinates → FormValue n k) ⊆ coordProj Γ '' tsupport g := by
        refine (closure_mono (image_mono ?_)).trans (h.projSupport_actSum_subset hg)
        intro x hx
        have hxp : x ∈ positiveCoordinates := by
          by_contra hn
          exact hx (Form.outside _ hn)
        rw [Function.mem_support] at hx ⊢
        rwa [hres x hxp] at hx
      have hcomp : IsCompact (coordProj Γ '' tsupport g) :=
        hg.2.1.image_of_continuousOn (continuousOn_coordProj.mono hg.2.2)
      exact hcomp.of_isClosed_subset isClosed_closure hsub⟩

theorem fn_avgForm (h : Admissible Γ) {g : Coordinates → FormValue n k} (hg : g ∈ Cc n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    CForm.fn (avgForm h g hg) x = actSum Γ n k g x :=
  restrictForm_apply _ (h.contDiffOn_actSum hg) hx

/-- Averaging as a linear map from compactly supported smooth forms to `CForm`. -/
def avg (h : Admissible Γ) : Cc n k →ₗ[ℝ] CForm Γ n k where
  toFun g := avgForm h g.1 g.2
  map_add' g g' := by
    apply CForm.ext
    intro x hx
    rw [CForm.fn_add, Pi.add_apply, fn_avgForm h _ hx, fn_avgForm h _ hx, fn_avgForm h _ hx]
    exact h.actSum_add g.2 g'.2 hx
  map_smul' c g := by
    apply CForm.ext
    intro x hx
    rw [CForm.fn_smul, Pi.smul_apply, RingHom.id_apply, fn_avgForm h _ hx, fn_avgForm h _ hx]
    exact h.actSum_smul g.2 c hx

theorem fn_avg (h : Admissible Γ) (g : Cc n k) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    CForm.fn (avg h g) x = actSum Γ n k g x :=
  fn_avgForm h g.2 hx

/-! ### Unfolding -/

/-- Unfolding of an integral over the orbit space whose integrand is a sum over translates. -/
theorem Admissible.integral_quotient_tsum (h : Admissible Γ) {H : Space → ℝ}
    (hHm : Measurable H) (hHi : Integrable H spaceVolume) {F : OrbitSpace Γ → ℝ}
    (hFc : Continuous F) (hF : ∀ S : Space, F (proj Γ S) = ∑' γ : Γ, H (γ • S)) :
    ∫ q, F q ∂quotientVolume Γ = ∫ S, H S ∂spaceVolume := by
  have : Countable Γ := h.countable
  obtain ⟨t, htm, ht⟩ := h.exists_isFundamentalDomain
  have h1 : ∫ q, F q ∂quotientVolume Γ = ∫ x in t, F (proj Γ x) ∂spaceVolume :=
    h.integral_quotientVolume ht hFc.measurable
  have h2 : ∫ S, H S ∂spaceVolume = ∑' g : Γ, ∫ x in t, H (g • x) ∂spaceVolume :=
    ht.integral_eq_tsum'' H hHi
  have hsm : ∀ g : Γ, Measurable (fun x : Space => H (g • x)) := fun g =>
    hHm.comp (measurable_const_smul g)
  have h3 : ∑' g : Γ, ∫ x in t, H (g • x) ∂spaceVolume =
      ∫ x in t, ∑' g : Γ, H (g • x) ∂spaceVolume := by
    symm
    apply integral_tsum (fun g => (hsm g).aestronglyMeasurable)
    have := ht.lintegral_eq_tsum'' (fun x => ‖H x‖ₑ)
    rw [← this]
    exact hHi.hasFiniteIntegral.ne
  rw [h1, h2, h3]
  exact setIntegral_congr_fun htm (fun x _ => hF x)

theorem formPairing_sum_left (n k : ℕ) (x : Coordinates) {ι : Type*} (s : Finset ι)
    (f : ι → FormValue n k) (b : FormValue n k) :
    formPairing n k x (∑ i ∈ s, f i) b = ∑ i ∈ s, formPairing n k x (f i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, formPairing_add_left, ih]

/-- The `L²` pairing of an average against an equivariant form is a plain coordinate integral. -/
theorem Admissible.l2Form_avg (h : Admissible Γ) {g : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) (b : CForm Γ n k) :
    l2Form Γ n k (avgForm h g hg) b =
      ∫ x in positiveCoordinates, coordinateDensity x * formPairing n k x (g x) (CForm.fn b x) := by
  set G : Coordinates → ℝ := fun x => formPairing n k x (g x) (CForm.fn b x) with hGdef
  have hGc : ContinuousOn G positiveCoordinates :=
    (contDiffOn_formPairing_functions n k (fun _ h => h) hg.1.contDiffOn
      (CForm.smooth b)).continuousOn
  have hGz : ∀ x, x ∉ tsupport g → G x = 0 := by
    intro x hx
    simp [hGdef, image_eq_zero_of_notMem_tsupport hx]
  rw [l2Form_apply, ← integral_chart G]
  apply h.integral_quotient_tsum
  · exact (hGc.comp_continuous continuous_chart_coordinates (fun S => extract_mem S)).measurable
  · exact integrable_chart hGc hg.2.1 hg.2.2 hGz
  · exact continuous_scalarPairing h _ _
  · intro S
    have hx : coordinateChart S ∈ positiveCoordinates := extract_mem S
    set x := coordinateChart S with hxdef
    rw [scalarPairing_proj h]
    have hfin := h.translates_finite hg.2.1 hg.2.2 hx
    let A : Finset Γ := hfin.toFinset
    have hA : ∀ γ : Γ, actPull n k (γ : RealGL) g x ≠ 0 → γ ∈ A := fun γ hγ =>
      hfin.mem_toFinset.mpr (actPull_ne_zero_mem g γ hx hγ)
    have hterm : ∀ γ : Γ, formPairing n k x (actPull n k (γ : RealGL) g x) (CForm.fn b x) =
        G (coordinateChart (γ • S)) := by
      intro γ
      have hc : coordinateChart (γ • S) = coordinateAction (γ : RealGL) x :=
        coordinateChart_act (γ : RealGL) S
      rw [hc]
      have hb := actPull_eq_of_equivariantAt n k (γ : RealGL) hx (CForm.equivariantAt b γ hx)
      calc formPairing n k x (actPull n k (γ : RealGL) g x) (CForm.fn b x)
          = formPairing n k x (actPull n k (γ : RealGL) g x)
              (actPull n k (γ : RealGL) (CForm.fn b) x) := by rw [hb]
        _ = G (coordinateAction (γ : RealGL) x) :=
            formPairing_actPull n k (γ : RealGL) (h.det_sq γ) g (CForm.fn b) hx
    show formPairing n k x (CForm.fn (avgForm h g hg) x) (CForm.fn b x) = _
    rw [fn_avgForm h hg hx, actSum_eq_sum_of_superset A hA, formPairing_sum_left]
    simp only [hterm]
    symm
    apply tsum_eq_sum
    intro γ hγ
    have : coordinateAction (γ : RealGL) x ∉ tsupport g := fun hmem =>
      hγ (hfin.mem_toFinset.mpr (by
        have hc : coordinateChart (γ • S) = coordinateAction (γ : RealGL) x :=
          coordinateChart_act (γ : RealGL) S
        exact hmem))
    have hc : coordinateChart (γ • S) = coordinateAction (γ : RealGL) x :=
      coordinateChart_act (γ : RealGL) S
    rw [hc]
    exact hGz _ this

/-! ### The norm of an average -/

theorem Admissible.overlap_finite (h : Admissible Γ) {K : Set Coordinates} (hK : IsCompact K)
    (hKp : K ⊆ positiveCoordinates) :
    {γ : Γ | ∃ y ∈ K, coordinateAction (γ : RealGL) y ∈ K}.Finite := by
  have hD := isCompact_chart_preimage hK hKp
  refine (h.transporters _ _ hD hD).subset ?_
  rintro γ ⟨y, hy, hγy⟩
  have hS : coordinateChart (coordinateChart.symm y) = y :=
    coordinateChart.right_inv (by simpa using hKp hy)
  refine ⟨γ • coordinateChart.symm y, ⟨coordinateChart.symm y, ?_, rfl⟩, ?_⟩
  · show coordinateChart (coordinateChart.symm y) ∈ K
    rwa [hS]
  · show coordinateChart (γ • coordinateChart.symm y) ∈ K
    rw [show coordinateChart (γ • coordinateChart.symm y) =
      coordinateAction (γ : RealGL) (coordinateChart (coordinateChart.symm y)) from
        coordinateChart_act (γ : RealGL) _, hS]
    exact hγy

theorem formPairing_two_mul_le (n k : ℕ) {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (a b : FormValue n k) :
    2 * formPairing n k x a b ≤ formPairing n k x a a + formPairing n k x b b := by
  have h0 := formPairing_nonneg n k x hx (a - b)
  have hsub : a - b = a + (-1 : ℝ) • b := by
    rw [sub_eq_add_neg]
    congr 1
    exact (neg_one_smul ℝ b).symm
  rw [hsub, formPairing_add_left, formPairing_add_right, formPairing_add_right,
    formPairing_smul_left, formPairing_smul_right, formPairing_smul_right, formPairing_smul_left,
    formPairing_symm n k x hx b a] at h0
  linarith

theorem integrable_pair (n k : ℕ) {f g : Coordinates → FormValue n k} (hf : f ∈ Cc n k)
    (hg : g ∈ Cc n k) :
    Integrable (fun x => coordinateDensity x * formPairing n k x (f x) (g x)) :=
  integrable_densityPairing n k hf.1.contDiffOn hg.1.contDiffOn hf.2.1 hf.2.2

theorem actPull_mem_Cc (n k : ℕ) (γ : RealGL) {g : Coordinates → FormValue n k} (hg : g ∈ Cc n k) :
    actPull n k γ g ∈ Cc n k :=
  ⟨contDiff_actPull n k γ hg.1.contDiffOn hg.2.1 hg.2.2, hasCompactSupport_actPull n k γ g hg.2.1 hg.2.2,
    tsupport_actPull_positive n k γ g hg.2.1 hg.2.2⟩

theorem formPairing_sum_right (n k : ℕ) (x : Coordinates) {ι : Type*} (s : Finset ι)
    (a : FormValue n k) (f : ι → FormValue n k) :
    formPairing n k x a (∑ i ∈ s, f i) = ∑ i ∈ s, formPairing n k x a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, formPairing_add_right, ih]

theorem setIntegral_pair_le (n k : ℕ) {f g : Coordinates → FormValue n k} (hf : f ∈ Cc n k)
    (hg : g ∈ Cc n k) :
    ∫ x in positiveCoordinates, coordinateDensity x * formPairing n k x (f x) (g x) ≤
      (localIntegral n k f f + localIntegral n k g g) / 2 := by
  have hf0 : ∀ x ∉ positiveCoordinates, f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hh => hx (hf.2.2 hh))
  have hg0 : ∀ x ∉ positiveCoordinates, g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hh => hx (hg.2.2 hh))
  rw [localIntegral_eq_setIntegral n k f f hf0, localIntegral_eq_setIntegral n k g g hg0]
  have hi1 := (integrable_pair n k hf hf).integrableOn (s := positiveCoordinates)
  have hi2 := (integrable_pair n k hg hg).integrableOn (s := positiveCoordinates)
  have hi3 := (integrable_pair n k hf hg).integrableOn (s := positiveCoordinates)
  rw [← integral_add hi1 hi2, ← integral_div]
  apply setIntegral_mono_on hi3 ((hi1.add hi2).div_const _) isOpen_positiveCoordinates.measurableSet
  intro x hx
  simp only [Pi.add_apply]
  have := formPairing_two_mul_le n k hx (f x) (g x)
  have hρ := (coordinateDensity_pos x hx).le
  nlinarith [mul_le_mul_of_nonneg_left this hρ]

/-- The squared `L²` norm of an average is at most the overlap number times the plain mass. -/
theorem Admissible.normSq_avgForm_le (h : Admissible Γ) {g : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) :
    normSq (avgForm h g hg) ≤
      ((h.overlap_finite hg.2.1 hg.2.2).toFinset.card : ℝ) * localIntegral n k g g := by
  classical
  set F := (h.overlap_finite hg.2.1 hg.2.2).toFinset with hF
  have hg0 : ∀ x ∉ positiveCoordinates, g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hh => hx (hg.2.2 hh))
  have hmass : ∀ γ : Γ, localIntegral n k (actPull n k (γ : RealGL) g) (actPull n k (γ : RealGL) g) =
      localIntegral n k g g := fun γ =>
    localIntegral_actPull n k (γ : RealGL) (h.det_sq γ) g g hg0
  have hpt : ∀ x ∈ positiveCoordinates, formPairing n k x (g x) (actSum Γ n k g x) =
      ∑ γ ∈ F, formPairing n k x (g x) (actPull n k (γ : RealGL) g x) := by
    intro x hx
    by_cases hgx : g x = 0
    · simp [hgx]
    · have hxK : x ∈ tsupport g := subset_tsupport _ hgx
      have hA : ∀ γ : Γ, actPull n k (γ : RealGL) g x ≠ 0 → γ ∈ F := fun γ hγ =>
        (h.overlap_finite hg.2.1 hg.2.2).mem_toFinset.mpr ⟨x, hxK, actPull_ne_zero_mem g γ hx hγ⟩
      rw [actSum_eq_sum_of_superset F hA, formPairing_sum_right]
  have hint : ∀ γ ∈ F, Integrable (fun x => coordinateDensity x *
      formPairing n k x (g x) (actPull n k (γ : RealGL) g x)) := fun γ _ =>
    integrable_pair n k hg (actPull_mem_Cc n k (γ : RealGL) hg)
  calc normSq (avgForm h g hg)
      = ∫ x in positiveCoordinates, coordinateDensity x *
          formPairing n k x (g x) (CForm.fn (avgForm h g hg) x) := h.l2Form_avg hg (avgForm h g hg)
    _ = ∫ x in positiveCoordinates, ∑ γ ∈ F, coordinateDensity x *
          formPairing n k x (g x) (actPull n k (γ : RealGL) g x) := by
        apply setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet
        intro x hx
        dsimp only
        rw [fn_avgForm h hg hx, hpt x hx, Finset.mul_sum]
    _ = ∑ γ ∈ F, ∫ x in positiveCoordinates, coordinateDensity x *
          formPairing n k x (g x) (actPull n k (γ : RealGL) g x) :=
        integral_finsetSum _ (fun γ hγ => (hint γ hγ).integrableOn)
    _ ≤ ∑ γ ∈ F, localIntegral n k g g := by
        apply Finset.sum_le_sum
        intro γ _
        have := setIntegral_pair_le n k hg (actPull_mem_Cc n k (γ : RealGL) hg)
        rw [hmass γ] at this
        linarith
    _ = (F.card : ℝ) * localIntegral n k g g := by rw [Finset.sum_const, nsmul_eq_mul]

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
