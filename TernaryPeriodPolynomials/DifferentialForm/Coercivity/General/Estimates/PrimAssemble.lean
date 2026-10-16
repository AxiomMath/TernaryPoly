module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.PrimLocal

@[expose] public section


/-! # General coercivity, Tier B (phase F): the gauge-corrected functional is smooth

Assembly of the local analysis: on a coordinate box `B` with compact closure the functional
`E = T - S ∘ δ` is represented by a smooth one-form.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.PolynomialFormWeakSmooth TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.CompactCoordinateIntegration
  TernaryPoly.SmoothCoveringDeRham TernaryPoly.PolynomialFormGeometricEnergy
  TernaryPoly.PolynomialFormConnection TernaryPoly.SmoothLocalDeRham
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n k : ℕ} {Γ : Subgroup RealGL}

theorem pairIn_add_form (Ω : TopologicalSpace.Opens Coordinates) {a b : Coordinates → FormValue n k}
    (ha : ContinuousOn a Ω) (hb : ContinuousOn b Ω) (g : CcIn n k (Ω : Set Coordinates)) :
    pairIn Ω (fun x => a x + b x) (ha.add hb) g = pairIn Ω a ha g + pairIn Ω b hb g := by
  rw [pairIn_apply, pairIn_apply, pairIn_apply, ← integral_add (integrable_pairing Ω a ha g)
    (integrable_pairing Ω b hb g)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  show coordinateDensity x * formPairing n k x (a x + b x) (g.1.1 x) = _
  rw [formPairing_add_left]
  ring

theorem pairIn_finset_sum (Ω : TopologicalSpace.Opens Coordinates) {ι : Type*} (s : Finset ι)
    (a : ι → Coordinates → FormValue n k) (ha : ∀ i, ContinuousOn (a i) Ω)
    (g : CcIn n k (Ω : Set Coordinates)) :
    pairIn Ω (fun x => ∑ i ∈ s, a i x) (continuousOn_finsetSum s fun i _ => ha i) g =
      ∑ i ∈ s, pairIn Ω (a i) (ha i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [pairIn_apply]
    simp
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    rw [← ih]
    exact pairIn_add_form Ω (ha j) (continuousOn_finsetSum s fun i _ => ha i) g

section Partition

variable (D : BoxData Γ)

theorem ucut_apply (p : Γ × D.ι) {y : Coordinates} (hy : y ∈ positiveCoordinates) :
    ucut D p y = D.ρ p.2 (coordinateAction ((p.1⁻¹ : Γ) : RealGL) y) := by
  unfold ucut
  rw [cutAct_apply _ _ hy, Subgroup.coe_inv]

theorem finsum_ucut (y : Coordinates) (hy : y ∈ positiveCoordinates) :
    ∑ᶠ p : Γ × D.ι, ucut D p y = 1 := by
  rw [← D.sum_one y hy]
  have e1 : ∀ p : Γ × D.ι, ucut D p y =
      (fun q : Γ × D.ι => D.ρ q.2 (coordinateAction (q.1 : RealGL) y))
        (Equiv.prodCongr (Equiv.inv Γ) (Equiv.refl D.ι) p) := fun p => ucut_apply D p hy
  simp only [e1]
  exact finsum_comp_equiv (Equiv.prodCongr (Equiv.inv Γ) (Equiv.refl D.ι))
    (f := fun q : Γ × D.ι => D.ρ q.2 (coordinateAction (q.1 : RealGL) y))

theorem sum_ucut_eq_one {K : Set Coordinates} (hfin : {p : Γ × D.ι | ∃ y ∈ tsupport (D.ρ p.2),
      coordinateAction (p.1 : RealGL) y ∈ K}.Finite) {y : Coordinates}
    (hyK : y ∈ K) (hy : y ∈ positiveCoordinates) : ∑ p ∈ hfin.toFinset, ucut D p y = 1 := by
  rw [← finsum_ucut D y hy]
  symm
  apply finsum_eq_sum_of_support_subset
  intro p hp
  rw [Finset.mem_coe, Set.Finite.mem_toFinset]
  rw [Function.mem_support, ucut_apply D p hy] at hp
  refine ⟨coordinateAction ((p.1⁻¹ : Γ) : RealGL) y, subset_tsupport _ hp, ?_⟩
  rw [show coordinateAction (p.1 : RealGL) (coordinateAction ((p.1⁻¹ : Γ) : RealGL) y) = y from ?_]
  · exact hyK
  · have := coordinateAction_inv_action (p.1⁻¹) hy
    simpa using this

theorem sum_mulCc_ucut {K : Set Coordinates} (hKp : K ⊆ positiveCoordinates)
    (hfin : {p : Γ × D.ι | ∃ y ∈ tsupport (D.ρ p.2), coordinateAction (p.1 : RealGL) y ∈ K}.Finite)
    (w : Cc n k) (hw : tsupport w.1 ⊆ K) :
    ∑ p ∈ hfin.toFinset, mulCc (ucut D p) (ucut_smooth D p) w = w := by
  apply Subtype.ext
  funext y
  have h1 : ((∑ p ∈ hfin.toFinset, mulCc (ucut D p) (ucut_smooth D p) w : Cc n k).1 :
      Coordinates → FormValue n k) y = ∑ p ∈ hfin.toFinset, ucut D p y • w.1 y := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [h1]
  by_cases hy : y ∈ tsupport w.1
  · rw [← fv_sum_smul, sum_ucut_eq_one D hfin (hw hy) (hKp (hw hy)), fv_one_smul]
  · have h0 : w.1 y = 0 := image_eq_zero_of_notMem_tsupport hy
    rw [h0]
    exact (Finset.sum_eq_zero fun p _ => fv_smul_zero _).trans rfl

theorem sum_commCc_ucut {K : Set Coordinates} (hKp : K ⊆ positiveCoordinates)
    (hfin : {p : Γ × D.ι | ∃ y ∈ tsupport (D.ρ p.2), coordinateAction (p.1 : RealGL) y ∈ K}.Finite)
    (g : Cc n (k + 1)) (hg : tsupport g.1 ⊆ K) :
    ∑ p ∈ hfin.toFinset, commCc (ucut D p) (ucut_smooth D p) g = 0 := by
  have h1 := sum_mulCc_ucut D hKp hfin g hg
  have h2 := sum_mulCc_ucut D hKp hfin (deltaCc n k g)
    ((tsupport_localAdjoint n k g.1).trans hg)
  have h3 : ∑ p ∈ hfin.toFinset, commCc (ucut D p) (ucut_smooth D p) g =
      ∑ p ∈ hfin.toFinset, mulCc (ucut D p) (ucut_smooth D p) (deltaCc n k g) -
        deltaCc n k (∑ p ∈ hfin.toFinset, mulCc (ucut D p) (ucut_smooth D p) g) := by
    rw [map_sum, ← Finset.sum_sub_distrib]
    rfl
  rw [h3, h1, h2, sub_self]

/-- `ρ_i · v`, a smooth form on the positive coordinates vanishing off `tsupport ρ_i`. -/
def Wfun (i : D.ι) (v : Coordinates → FormValue n k) : Coordinates → FormValue n k :=
  fun y => D.ρ i y • v y

theorem Wfun_zero_outside (i : D.ι) (v : Coordinates → FormValue n k) {y : Coordinates}
    (hy : y ∉ positiveCoordinates) : Wfun D i v y = 0 := by
  have : D.ρ i y = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hy (D.box_pos i (D.tsupport_subset i h)))
  change D.ρ i y • v y = 0
  rw [this]
  exact ContinuousAlternatingMap.ext fun w => by simp

theorem contDiffOn_Wfun (i : D.ι) {v : Coordinates → FormValue n k}
    (hv : ContDiffOn ℝ ∞ v (D.box i)) : ContDiffOn ℝ ∞ (Wfun D i v) positiveCoordinates := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  by_cases hxb : x ∈ (D.box i : Set Coordinates)
  · refine ⟨D.box i, (D.box i).isOpen, hxb, ?_⟩
    let : IsBoundedSMul ℝ (FormValue n k) :=
      @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
    exact ((D.smooth i).contDiffOn.smul hv).mono inter_subset_right
  · have hxt : x ∉ tsupport (D.ρ i) := fun h => hxb (D.tsupport_subset i h)
    refine ⟨(tsupport (D.ρ i))ᶜ, (isClosed_tsupport _).isOpen_compl, hxt, ?_⟩
    refine (contDiffOn_const (c := (0 : FormValue n k))).congr (fun y hy => ?_) |>.mono inter_subset_right
    have : D.ρ i y = 0 := image_eq_zero_of_notMem_tsupport hy
    change D.ρ i y • v y = 0
    rw [this]
    exact ContinuousAlternatingMap.ext fun w => by simp

theorem cutLin_delta (h : Admissible Γ) (B : TopologicalSpace.Opens Coordinates) (p : Γ × D.ι)
    (g : CcIn n 1 (B : Set Coordinates)) :
    cutLin D p (deltaCc n 0 g.1) =
      deltaIn n 0 (D.box p.2 : Set Coordinates) (cutLin D p g.1) + qI D B p g := by
  have hγ : (p.1 : RealGL).val.det ^ 2 = 1 := h.det_sq p.1
  apply Subtype.ext
  change mulCc (D.ρ p.2) (D.smooth p.2) (pullCc (p.1 : RealGL) (deltaCc n 0 g.1)) =
    deltaCc n 0 (mulCc (D.ρ p.2) (D.smooth p.2) (pullCc (p.1 : RealGL) g.1)) +
      pullCc (p.1 : RealGL) (commCc (ucut D p) (ucut_smooth D p) g.1)
  have hc := commCc_pullCc (p.1 : RealGL) hγ (D.smooth p.2) (D.compact p.2) (tsupport_ρ_pos D p.2) g.1
  have hu : ucut D p = cutAct (p.1 : RealGL)⁻¹ (D.ρ p.2) := rfl
  have e : pullCc (p.1 : RealGL) (commCc (ucut D p) (ucut_smooth D p) g.1) =
      commCc (D.ρ p.2) (D.smooth p.2) (pullCc (p.1 : RealGL) g.1) := hc.symm
  rw [e, ← deltaCc_pullCc _ hγ]
  simp only [commCc, LinearMap.sub_apply, LinearMap.comp_apply]
  abel

theorem integral_cut_pair (h : Admissible Γ) (i : D.ι) (γ : Γ) (v : Coordinates → FormValue n 1)
    (g : Cc n 1) :
    ∫ x, coordinateDensity x * formPairing n 1 x (v x) ((cutLin D (γ, i) g).1.1 x) =
      ∫ x, coordinateDensity x * formPairing n 1 x
        (actPull n 1 ((γ : RealGL)⁻¹) (Wfun D i v) x) (g.1 x) := by
  have hγ : (γ : RealGL).val.det ^ 2 = 1 := h.det_sq γ
  have h1 : ∫ x, coordinateDensity x * formPairing n 1 x (v x) ((cutLin D (γ, i) g).1.1 x) =
      localIntegral n 1 (Wfun D i v) (actPull n 1 (γ : RealGL) g.1) := by
    unfold localIntegral
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    change coordinateDensity x * formPairing n 1 x (v x) (D.ρ i x • actPull n 1 (γ : RealGL) g.1 x) =
      coordinateDensity x * formPairing n 1 x (D.ρ i x • v x) (actPull n 1 (γ : RealGL) g.1 x)
    rw [formPairing_smul_right, formPairing_smul_left]
  rw [h1, localIntegral_actPull_right n 1 _ hγ (Wfun D i v) g.1 (fun x hx => Wfun_zero_outside D i v hx)]
  rfl

end Partition

/-- **The gauge-corrected functional is smooth on a box.**  On a coordinate box `B` with compact
closure the functional `E = T - S ∘ δ` is represented by a smooth one-form. -/
theorem corrected_local (h : Admissible Γ) (D : BoxData Γ) (T : Cc n 1 →ₗ[ℝ] ℝ)
    (hinv : ∀ (δ : Γ) (g : Cc n 1), T (pullCc (δ : RealGL) g) = T g)
    (G : ∀ i : D.ι, LocalPrim (D.box i) T) (B : TopologicalSpace.Opens Coordinates)
    (hBcl : closure (B : Set Coordinates) ⊆ positiveCoordinates)
    (hBc : IsCompact (closure (B : Set Coordinates))) (GB : LocalPrim B T) :
    ∃ (η : Coordinates → FormValue n 1) (hη : ContDiffOn ℝ ∞ η B),
      ∀ g : CcIn n 1 (B : Set Coordinates),
        corrected D (fun i => (G i).S) T g.1 = pairIn B η hη.continuousOn g := by
  classical
  have hBpos : (B : Set Coordinates) ⊆ positiveCoordinates := subset_closure.trans hBcl
  have hfin := D.finite_pairs hBc hBcl
  set P := hfin.toFinset with hP
  choose ηp hηp hrep using fun p : Γ × D.ι => per_p D B h T hinv p hBpos GB (G p.2)
  let vpart : Γ × D.ι → Coordinates → FormValue n 1 := fun p =>
    actPull n 1 ((p.1 : RealGL)⁻¹) (Wfun D p.2 (G p.2).v)
  have hvpart : ∀ p, ContDiffOn ℝ ∞ (vpart p) positiveCoordinates := fun p =>
    contDiffOn_actPull n 1 _ (contDiffOn_Wfun D p.2 (G p.2).hv)
  let η : Coordinates → FormValue n 1 := fun x => ∑ p ∈ P, (vpart p x + ηp p x)
  have hη : ContDiffOn ℝ ∞ η B :=
    ContDiffOn.sum fun p _ => ((hvpart p).mono hBpos).add (hηp p)
  refine ⟨η, hη, fun g => ?_⟩
  let S : ∀ i : D.ι, CcIn n 0 (D.box i : Set Coordinates) →ₗ[ℝ] ℝ := fun i => (G i).S
  -- the right-hand side
  have hR : pairIn B η hη.continuousOn g = ∑ p ∈ P, (pairIn B (vpart p) ((hvpart p).mono hBpos).continuousOn g +
      (GB.S (qB D B p g) - (G p.2).S (qI D B p g))) := by
    have e1 : pairIn B η hη.continuousOn g =
        ∑ p ∈ P, pairIn B (fun x => vpart p x + ηp p x)
          (((hvpart p).mono hBpos).add (hηp p)).continuousOn g :=
      pairIn_finset_sum B P (fun p x => vpart p x + ηp p x)
        (fun p => (((hvpart p).mono hBpos).add (hηp p)).continuousOn) g
    refine e1.trans (Finset.sum_congr rfl fun p _ => ?_)
    exact (pairIn_add_form B ((hvpart p).mono hBpos).continuousOn (hηp p).continuousOn g).trans
      (congrArg (fun r : ℝ => pairIn B (vpart p) ((hvpart p).mono hBpos).continuousOn g + r)
        (hrep p g).symm)
  -- the terms of the gauge
  have hterm : ∀ p ∈ P, gaugeTerm D S p (deltaCc n 0 g.1) =
      T (mulCc (ucut D p) (ucut_smooth D p) g.1) -
        pairIn B (vpart p) ((hvpart p).mono hBpos).continuousOn g + (G p.2).S (qI D B p g) := by
    intro p _
    change (G p.2).S (cutLin D p (deltaCc n 0 g.1)) = _
    have e1 : (G p.2).S (cutLin D p (deltaCc n 0 g.1)) =
        (G p.2).S (deltaIn n 0 (D.box p.2 : Set Coordinates) (cutLin D p g.1)) +
          (G p.2).S (qI D B p g) :=
      (congrArg (G p.2).S (cutLin_delta D h B p g)).trans ((G p.2).S.map_add _ _)
    have hprim := (G p.2).prim (cutLin D p g.1)
    have hT : T (cutLin D p g.1).1 = T (mulCc (ucut D p) (ucut_smooth D p) g.1) := by
      change T (mulCc (D.ρ p.2) (D.smooth p.2) (pullCc (p.1 : RealGL) g.1)) = _
      rw [mulCc_pullCc (p.1 : RealGL) (D.smooth p.2) (D.compact p.2) (tsupport_ρ_pos D p.2), hinv]
      rfl
    have hp : pairIn (D.box p.2) (G p.2).v (G p.2).hv.continuousOn (cutLin D p g.1) =
        pairIn B (vpart p) ((hvpart p).mono hBpos).continuousOn g := by
      exact (pairIn_apply _ _ _ _).trans
        ((integral_cut_pair D h p.2 p.1 (G p.2).v g.1).trans (pairIn_apply _ _ _ _).symm)
    have e2 : (G p.2).S (deltaIn n 0 (D.box p.2 : Set Coordinates) (cutLin D p g.1)) =
        T (mulCc (ucut D p) (ucut_smooth D p) g.1) -
          pairIn B (vpart p) ((hvpart p).mono hBpos).continuousOn g :=
      (eq_sub_of_add_eq' hprim.symm).trans (congrArg₂ (fun a b : ℝ => a - b) hT hp)
    exact e1.trans (congrArg (fun r : ℝ => r + (G p.2).S (qI D B p g)) e2)
  have hvanish : ∀ p, p ∉ P → gaugeTerm D S p (deltaCc n 0 g.1) = 0 := by
    intro p hp
    have : cutLin D p (deltaCc n 0 g.1) = 0 := by
      apply cutLin_eq_zero
      intro y hy hyf
      apply hp
      rw [hP, Set.Finite.mem_toFinset]
      exact ⟨y, hy, subset_closure ((((tsupport_localAdjoint n 0 g.1.1)) hyf |> fun hh => g.2 hh))⟩
    change (G p.2).S (cutLin D p (deltaCc n 0 g.1)) = 0
    rw [this, map_zero]
  have hGauge := gaugeLin_eq_sum D S (deltaCc n 0 g.1) P hvanish
  have hTsum : T g.1 = ∑ p ∈ P, T (mulCc (ucut D p) (ucut_smooth D p) g.1) := by
    conv_lhs => rw [← sum_mulCc_ucut D hBcl hfin g.1 (g.2.trans subset_closure)]
    exact map_sum T _ _
  have hGB : ∑ p ∈ P, GB.S (qB D B p g) = 0 := by
    rw [← map_sum]
    have : ∑ p ∈ P, qB D B p g = 0 := by
      apply Subtype.ext
      have h0 := sum_commCc_ucut D hBcl hfin g.1 (g.2.trans subset_closure)
      change ((∑ p ∈ P, qB D B p g : CcIn n 0 (B : Set Coordinates)) : Cc n 0) = 0
      rw [Submodule.coe_sum]
      exact h0
    rw [this, map_zero]
  have eC : corrected D (fun i => (G i).S) T g.1 =
      T g.1 - ∑ p ∈ P, gaugeTerm D S p (deltaCc n 0 g.1) :=
    (corrected_apply D (fun i => (G i).S) T g.1).trans
      (congrArg (fun r : ℝ => T g.1 - r) hGauge)
  refine eC.trans (Eq.trans ?_ hR.symm)
  refine (congrArg (fun r : ℝ => T g.1 - r) (Finset.sum_congr rfl hterm)).trans ?_
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hTsum hGB ⊢
  linarith

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
