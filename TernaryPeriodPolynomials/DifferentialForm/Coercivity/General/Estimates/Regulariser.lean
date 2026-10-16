module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.RegBasic
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.LocalFriedrichs
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.LocalOperators
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.LocalTranspose
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.FriedrichsStep

@[expose] public section


/-! # General coercivity, Tier B: the equivariant regulariser

For a compact set `Q` of the orbit space, a cutoff partition `χ` over `Q` and companion cutoffs
`η, θ`, the regulariser of an equivariant form `a` is `r_c a = Π (η (κ_c ∗ (χ a)))`, the average over
`Γ` of the cutoff mollification of `χ a` in the single global coordinate chart.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set MeasureTheory Filter Topology TernaryPoly TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian
open scoped ContDiff

variable {Γ : Subgroup RealGL} {n : ℕ}

/-- Cutoffs adapted to a compact subset `Q` of the orbit space. -/
structure RegData (Γ : Subgroup RealGL) (Q : Set (OrbitSpace Γ)) where
  C : Cuts
  cut : CutoffData Γ Q C.χ

variable [hΓ : Fact (Admissible Γ)] {Q : Set (OrbitSpace Γ)} (R : RegData Γ Q)

/-- The mollification of the cutoff of an equivariant form, as a compactly supported smooth form. -/
def RegData.Mol (p : ℕ) {c : ℝ} (hc : 0 < c) : CForm Γ n p →ₗ[ℝ] Cc n p where
  toFun a := ⟨frMol n p R.C.χ R.C.η c (CForm.fn a),
    contDiff_frMol R.C.χ_smooth R.C.χ_pos R.C.η_smooth hc.ne' (CForm.smooth a),
    hasCompactSupport_frMol R.C.η_compact c _,
    (tsupport_frMol_subset R.C.χ R.C.η c _).trans R.C.η_pos⟩
  map_add' a a' := Subtype.ext (funext fun x =>
    frMol_add R.C.χ_smooth R.C.χ_compact R.C.χ_pos c (CForm.smooth a) (CForm.smooth a') x)
  map_smul' r a := Subtype.ext (funext fun x => frMol_smul R.C.χ R.C.η c r (CForm.fn a) x)

/-- The regulariser at scale `c`. -/
def RegData.reg (p : ℕ) {c : ℝ} (hc : 0 < c) : CForm Γ n p →ₗ[ℝ] CForm Γ n p :=
  (avg hΓ.out).comp (R.Mol p hc)

theorem RegData.fn_reg (p : ℕ) {c : ℝ} (hc : 0 < c) (a : CForm Γ n p) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    CForm.fn (R.reg p hc a) x = actSum Γ n p (frMol n p R.C.χ R.C.η c (CForm.fn a)) x :=
  fn_avg hΓ.out (R.Mol p hc a) hx

/-- Adapted cutoffs exist for every compact set of the orbit space. -/
theorem RegData.exists (hQ : IsCompact Q) : Nonempty (RegData Γ Q) := by
  obtain ⟨φ, hφ⟩ := hΓ.out.exists_cutoff hQ
  have hKφ : IsCompact (tsupport φ) := hφ.compactSupport.isCompact
  obtain ⟨η, hη, hcη, hsη, hη1⟩ :=
    CompactSmoothCutoff.exists_cutoff hKφ isOpen_positiveCoordinates hφ.tsupport_subset
  have hK2 : IsCompact (tsupport φ ∪ tsupport η) := hKφ.union hcη.isCompact
  obtain ⟨θ, hθ, hcθ, hsθ, hθ1⟩ := CompactSmoothCutoff.exists_cutoff hK2
    isOpen_positiveCoordinates (union_subset hφ.tsupport_subset hsη)
  obtain ⟨M, hM⟩ := hcη.exists_bound_of_continuous hη.continuous
  let C : Cuts :=
    { χ := φ
      η := η
      θ := θ
      χ_smooth := hφ.smooth
      η_smooth := hη
      θ_smooth := hθ
      χ_compact := hφ.compactSupport
      η_compact := hcη
      θ_compact := hcθ
      χ_pos := hφ.tsupport_subset
      η_pos := hsη
      θ_pos := hsθ
      η_one := hη1
      θ_one := hθ1
      M := max M 0
      M_nonneg := le_max_right _ _
      η_bound := fun x => (hM x).trans (le_max_left _ _) }
  exact ⟨⟨C, hφ⟩⟩

omit hΓ in
theorem actSum_cut_eq {p : ℕ} (hφ : CutoffData Γ Q R.C.χ) {a : CForm Γ n p} {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    actSum Γ n p (fun y => R.C.χ y • CForm.fn a y) x =
      (∑ᶠ γ : Γ, R.C.χ (coordinateAction (γ : RealGL) x)) • CForm.fn a x := by
  classical
  obtain ⟨N, hN, -, hfin⟩ := hφ.locallyFinite x hx
  let S : Set Γ := {γ : Γ | R.C.χ (coordinateAction (γ : RealGL) x) ≠ 0}
  have hS : S.Finite := hfin.subset fun γ hγ => ⟨x, mem_of_mem_nhds hN, hγ⟩
  have h1 : ∀ γ : Γ, actPull n p (γ : RealGL) (fun y => R.C.χ y • CForm.fn a y) x =
      R.C.χ (coordinateAction (γ : RealGL) x) • CForm.fn a x := fun γ =>
    (actPull_fun_smul n p (γ : RealGL) R.C.χ (CForm.fn a) hx).trans
      (congrArg (fun z : FormValue n p => R.C.χ (coordinateAction (γ : RealGL) x) • z)
        (actPull_eq_of_equivariantAt n p (γ : RealGL) hx (CForm.equivariantAt a γ hx)))
  have h2 : (∑ᶠ γ : Γ, R.C.χ (coordinateAction (γ : RealGL) x)) =
      ∑ γ ∈ hS.toFinset, R.C.χ (coordinateAction (γ : RealGL) x) :=
    finsum_eq_sum_of_support_subset _ (fun γ hγ => hS.mem_toFinset.mpr hγ)
  have h3 : actSum Γ n p (fun y => R.C.χ y • CForm.fn a y) x =
      ∑ γ ∈ hS.toFinset, R.C.χ (coordinateAction (γ : RealGL) x) • CForm.fn a x := by
    unfold actSum
    simp only [h1]
    refine finsum_eq_sum_of_support_subset _ (fun γ hγ => hS.mem_toFinset.mpr ?_)
    intro h0
    apply hγ
    show R.C.χ (coordinateAction (γ : RealGL) x) • CForm.fn a x = 0
    rw [h0]
    exact zero_smul_fv _
  rw [h3, h2]
  exact (Finset.sum_smul (s := hS.toFinset) (f := fun γ : Γ => R.C.χ (coordinateAction (γ : RealGL) x))
    (x := CForm.fn a x)).symm

omit hΓ in
theorem RegData.cutMem (p : ℕ) (a : CForm Γ n p) :
    (fun y => R.C.χ y • CForm.fn a y) ∈ Cc n p :=
  cut_mem_Cc R.C.χ_smooth R.C.χ_compact R.C.χ_pos (CForm.smooth a)

/-- On forms supported over `Q` the cutoff partition averages back to the form. -/
theorem RegData.avg_cut_eq_self (p : ℕ) {a : CForm Γ n p} (ha : a ∈ SuppIn Q n p) :
    avg hΓ.out (⟨fun y => R.C.χ y • CForm.fn a y, R.cutMem p a⟩ : Cc n p) = a := by
  apply CForm.ext
  intro x hx
  refine (fn_avg hΓ.out _ hx).trans ((actSum_cut_eq R R.cut hx).trans ?_)
  by_cases h0 : CForm.fn a x = 0
  · rw [h0]
    exact smul_zero (A := FormValue n p) (∑ᶠ γ : Γ, R.C.χ (coordinateAction (γ : RealGL) x))
  · have hxQ : coordProj Γ x ∈ Q := ha x hx h0
    obtain ⟨W, -, -, hW, hsum⟩ := R.cut.partition
    have h1 : (∑ᶠ γ : Γ, R.C.χ (coordinateAction (γ : RealGL) x)) = 1 := hsum x (hW x hx hxQ)
    rw [h1]
    exact one_smul_fv _

theorem tendsto_of_sq_norm_tendsto_zero {E : Type*} [NormedAddCommGroup E] {f : ℕ → E} {b : E}
    (h : Tendsto (fun j => ‖f j - b‖ ^ 2) atTop (𝓝 0)) : Tendsto f atTop (𝓝 b) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h' := (Real.continuous_sqrt.tendsto 0).comp h
  change Tendsto (fun j => Real.sqrt (‖f j - b‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at h'
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h'

/-- The regulariser at scale `j + 1`. -/
def RegData.regSeq (p : ℕ) (j : ℕ) : CForm Γ n p →ₗ[ℝ] CForm Γ n p :=
  R.reg p (c := (j : ℝ) + 1) (by positivity)

/-- The average of the cutoff of a form. -/
def RegData.avgCut (p : ℕ) (a : CForm Γ n p) : CForm Γ n p :=
  avg hΓ.out (⟨fun y => R.C.χ y • CForm.fn a y, R.cutMem p a⟩ : Cc n p)

omit hΓ in
theorem RegData.η_eq_one {y : Coordinates} (hy : y ∈ tsupport R.C.χ) : R.C.η y = 1 :=
  (R.C.η_one y hy).self_of_nhds.trans (Pi.one_apply y)

omit hΓ in
theorem RegData.tsupport_χ_sub_η : tsupport R.C.χ ⊆ tsupport R.C.η := fun y hy =>
  subset_tsupport R.C.η (by
    rw [Function.mem_support, R.η_eq_one hy]
    exact one_ne_zero)

omit hΓ in
theorem RegData.eta_cut {p : ℕ} (f : Coordinates → FormValue n p) :
    (fun y => R.C.η y • (R.C.χ y • f y)) = fun y => R.C.χ y • f y := by
  funext y
  by_cases hy : y ∈ tsupport R.C.χ
  · exact (congrArg (fun r : ℝ => r • (R.C.χ y • f y)) (R.η_eq_one hy)).trans
      (one_smul_fv _)
  · have h0 : R.C.χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have e1 : R.C.χ y • f y = 0 := (congrArg (fun r : ℝ => r • f y) h0).trans (zero_smul_fv _)
    exact (congrArg (fun z : FormValue n p => R.C.η y • z) e1).trans
      ((smul_zero (A := FormValue n p) (R.C.η y)).trans e1.symm)

theorem RegData.norm_sq_sub_le (p : ℕ) {c : ℝ} (hc : 0 < c) (a : CForm Γ n p) :
    ‖incl Γ n p (R.reg p hc a) - incl Γ n p (R.avgCut p a)‖ ^ 2 ≤
      ((hΓ.out.overlap_finite R.C.η_compact.isCompact R.C.η_pos).toFinset.card : ℝ) *
        wL2 (fun y => frMol n p R.C.χ R.C.η c (CForm.fn a) y -
          R.C.η y • (R.C.χ y • CForm.fn a y)) := by
  classical
  have h := hΓ.out
  have hgg : ((R.Mol p hc a).1 - fun y => R.C.χ y • CForm.fn a y) ∈ Cc n p :=
    (Cc n p).sub_mem (R.Mol p hc a).2 (R.cutMem p a)
  have e1 : incl Γ n p (R.reg p hc a) - incl Γ n p (R.avgCut p a) =
      incl Γ n p (avgForm h _ hgg) := by
    have e : avgForm h _ hgg = R.reg p hc a - R.avgCut p a :=
      (map_sub (avg h) (R.Mol p hc a) (⟨fun y => R.C.χ y • CForm.fn a y, R.cutMem p a⟩ : Cc n p))
    exact ((congrArg (incl Γ n p) e).trans (map_sub (incl Γ n p) _ _)).symm
  have hsub : tsupport ((R.Mol p hc a).1 - fun y => R.C.χ y • CForm.fn a y) ⊆ tsupport R.C.η :=
    (tsupport_sub _ _).trans (union_subset (tsupport_frMol_subset R.C.χ R.C.η c _)
      ((tsupport_cut_subset R.C.χ _).trans R.tsupport_χ_sub_η))
  have h2 := h.normSq_avgForm_le_of_subset hgg R.C.η_compact.isCompact R.C.η_pos hsub
  have e3 : ((R.Mol p hc a).1 - fun y => R.C.χ y • CForm.fn a y) =
      fun y => frMol n p R.C.χ R.C.η c (CForm.fn a) y - R.C.η y • (R.C.χ y • CForm.fn a y) := by
    funext y
    exact congrArg (fun z : FormValue n p => frMol n p R.C.χ R.C.η c (CForm.fn a) y - z)
      (congrFun (R.eta_cut (CForm.fn a)) y).symm
  exact (congrArg (fun z : Hilbert Γ n p => ‖z‖ ^ 2) e1).trans_le
    ((norm_incl_sq Γ n p _).trans_le (h2.trans_eq (congrArg (fun G => _ * wL2 G) e3)))

theorem tendsto_natCast_add_one_atTop : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

theorem RegData.regSeq_tendsto (p : ℕ) (a : CForm Γ n p) :
    Tendsto (fun j => incl Γ n p (R.regSeq p j a)) atTop (𝓝 (incl Γ n p (R.avgCut p a))) := by
  apply tendsto_of_sq_norm_tendsto_zero
  have hlim : Tendsto (fun j : ℕ => ((hΓ.out.overlap_finite R.C.η_compact.isCompact
      R.C.η_pos).toFinset.card : ℝ) * wL2 (fun y => frMol n p R.C.χ R.C.η ((j : ℝ) + 1)
        (CForm.fn a) y - R.C.η y • (R.C.χ y • CForm.fn a y))) atTop (𝓝 0) := by
    have h := (frMol_weighted_tendsto R.C.χ_smooth R.C.χ_compact R.C.χ_pos R.C.η_smooth
      R.C.η_compact R.C.η_pos (CForm.smooth a)).comp tendsto_natCast_add_one_atTop
    have h' := h.const_mul ((hΓ.out.overlap_finite R.C.η_compact.isCompact
      R.C.η_pos).toFinset.card : ℝ)
    rw [mul_zero] at h'
    exact h'
  exact squeeze_zero' (Eventually.of_forall fun j => sq_nonneg _)
    (Eventually.of_forall fun j => R.norm_sq_sub_le p (by positivity) a) hlim

theorem exists_abs_bound {ψ : Coordinates → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ∃ Λ : ℝ, ∀ y, |ψ y| ≤ Λ := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hψ
  exact ⟨C, fun y => by simpa only [Real.norm_eq_abs] using hC y⟩

theorem aux_chain3 {x w c1 w1 y Nη Aw Ac N3 : ℝ} (hN : 0 ≤ Nη) (hAw : 0 ≤ Aw) (hAc : 0 ≤ Ac)
    (_hN3 : 0 ≤ N3) (h1 : x ≤ Nη * w) (h2 : w ≤ Aw * c1) (h4 : c1 ≤ Ac * w1)
    (h5 : w1 ≤ N3 * y) : x ≤ Nη * Aw * Ac * N3 * y := by
  have h6 : c1 ≤ Ac * (N3 * y) := h4.trans (mul_le_mul_of_nonneg_left h5 hAc)
  have h7 : w ≤ Aw * (Ac * (N3 * y)) := h2.trans (mul_le_mul_of_nonneg_left h6 hAw)
  have h8 : x ≤ Nη * (Aw * (Ac * (N3 * y))) := h1.trans (mul_le_mul_of_nonneg_left h7 hN)
  calc x ≤ Nη * (Aw * (Ac * (N3 * y))) := h8
    _ = Nη * Aw * Ac * N3 * y := by ring

omit hΓ in
theorem RegData.exists_Aw (p : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {c : ℝ}, 0 < c → ∀ {f : Coordinates → FormValue n p},
      ContDiffOn ℝ ∞ f positiveCoordinates →
      wL2 (frMol n p R.C.χ R.C.η c f) ≤ A * compL2 (fun y => R.C.χ y • f y) :=
  exists_wL2_frMol_le R.C.χ_smooth R.C.χ_compact R.C.χ_pos R.C.η_smooth R.C.η_compact R.C.η_pos
    R.C.M_nonneg R.C.η_bound

omit hΓ in
theorem RegData.exists_Ac (p : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ g : Coordinates → FormValue n p, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ tsupport R.C.χ → wL2 g ≤ A * compL2 g ∧ compL2 g ≤ A * wL2 g :=
  exists_wL2_comp n p R.C.χ_compact.isCompact R.C.χ_pos

theorem RegData.exists_N3 (p : ℕ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ a : CForm Γ n p, wL2 (fun y => R.C.χ y • CForm.fn a y) ≤ N * normSq a := by
  have hΛ := exists_abs_bound R.C.χ_smooth.continuous R.C.χ_compact
  exact wL2_cut_le (Γ := Γ) (n := n) (k := p) R.C.χ_smooth R.C.χ_compact R.C.χ_pos hΛ.choose_spec

/-- The regularisers are uniformly bounded in the scale. -/
theorem RegData.exists_normSq_reg_le (p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {c : ℝ} (hc : 0 < c) (a : CForm Γ n p),
      normSq (R.reg p hc a) ≤ K * normSq a := by
  have h := hΓ.out
  have hw := R.exists_Aw (n := n) p
  have hc := R.exists_Ac (n := n) p
  have h3 := R.exists_N3 (n := n) p
  have hNη : 0 ≤ ((h.overlap_finite R.C.η_compact.isCompact R.C.η_pos).toFinset.card : ℝ) :=
    Nat.cast_nonneg _
  refine ⟨((h.overlap_finite R.C.η_compact.isCompact R.C.η_pos).toFinset.card : ℝ) *
    hw.choose * hc.choose * h3.choose,
    mul_nonneg (mul_nonneg (mul_nonneg hNη hw.choose_spec.1) hc.choose_spec.1) h3.choose_spec.1,
    fun {c} hc0 a => ?_⟩
  have h1 : normSq (R.reg p hc0 a) ≤ ((h.overlap_finite R.C.η_compact.isCompact
      R.C.η_pos).toFinset.card : ℝ) * wL2 (frMol n p R.C.χ R.C.η c (CForm.fn a)) :=
    h.normSq_avgForm_le_of_subset (R.Mol p hc0 a).2 R.C.η_compact.isCompact R.C.η_pos
      (tsupport_frMol_subset R.C.χ R.C.η c _)
  have h2 := hw.choose_spec.2 hc0 (CForm.smooth a)
  have hcg := R.cutMem p a
  have h4 := (hc.choose_spec.2 _ hcg.1 hcg.2.1 ((tsupport_cut_subset R.C.χ _))).2
  have h5 := h3.choose_spec.2 a
  exact aux_chain3 hNη hw.choose_spec.1 hc.choose_spec.1 h3.choose_spec.1 h1 h2 h4 h5

theorem RegData.norm_regSeq_le (p : ℕ) (j : ℕ) (a : CForm Γ n p) :
    ‖incl Γ n p (R.regSeq p j a)‖ ≤
      Real.sqrt (R.exists_normSq_reg_le (n := n) p).choose * ‖incl Γ n p a‖ := by
  have hK := (R.exists_normSq_reg_le (n := n) p).choose_spec
  have hc : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h1 : normSq (R.regSeq p j a) ≤ (R.exists_normSq_reg_le (n := n) p).choose * normSq a :=
    hK.2 hc a
  have e : (Real.sqrt (R.exists_normSq_reg_le (n := n) p).choose * ‖incl Γ n p a‖) ^ 2 =
      (R.exists_normSq_reg_le (n := n) p).choose * normSq a :=
    (mul_pow _ _ 2).trans (congrArg₂ (· * ·) (Real.sq_sqrt hK.1) (norm_incl_sq Γ n p a))
  have hsq : ‖incl Γ n p (R.regSeq p j a)‖ ^ 2 ≤
      (Real.sqrt (R.exists_normSq_reg_le (n := n) p).choose * ‖incl Γ n p a‖) ^ 2 :=
    (norm_incl_sq Γ n p (R.regSeq p j a)).trans_le (h1.trans_eq e.symm)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq

/-- The regularisers at scales `1, 2, 3, …` as a bounded, convergent family. -/
def RegData.regFamily (p : ℕ) : RegFamily Γ n p where
  r := R.regSeq p
  K := Real.sqrt (R.exists_normSq_reg_le (n := n) p).choose
  K_nonneg := Real.sqrt_nonneg _
  bound := R.norm_regSeq_le p
  conv := fun a => ⟨_, R.regSeq_tendsto p a⟩

/-- The transpose of the regulariser for the `L²` pairing. -/
def RegData.trans (p : ℕ) {c : ℝ} (hc : 0 < c) (b : CForm Γ n p) : CForm Γ n p :=
  avgForm hΓ.out (frTr n p R.C.χ R.C.η c (CForm.fn b))
    ⟨contDiff_frTr R.C.χ_smooth R.C.χ_pos R.C.η_smooth R.C.η_pos hc.ne' (CForm.smooth b),
      hasCompactSupport_frTr R.C.χ_compact c _,
      (tsupport_frTr_subset R.C.χ R.C.η c _).trans R.C.χ_pos⟩

theorem RegData.inner_reg_trans (p : ℕ) {c : ℝ} (hc : 0 < c) (a b : CForm Γ n p) :
    inner ℝ (incl Γ n p (R.reg p hc a)) (incl Γ n p b) =
      inner ℝ (incl Γ n p a) (incl Γ n p (R.trans p hc b)) := by
  have h := hΓ.out
  have hM := (R.Mol p hc a).2
  have hT : frTr n p R.C.χ R.C.η c (CForm.fn b) ∈ Cc n p :=
    ⟨contDiff_frTr R.C.χ_smooth R.C.χ_pos R.C.η_smooth R.C.η_pos hc.ne' (CForm.smooth b),
      hasCompactSupport_frTr R.C.χ_compact c _,
      (tsupport_frTr_subset R.C.χ R.C.η c _).trans R.C.χ_pos⟩
  have h1 : l2Form Γ n p (R.reg p hc a) b = ∫ x in positiveCoordinates,
      coordinateDensity x * formPairing n p x (frMol n p R.C.χ R.C.η c (CForm.fn a) x)
        (CForm.fn b x) := h.l2Form_avg hM b
  have h2 : localIntegral n p (frMol n p R.C.χ R.C.η c (CForm.fn a)) (CForm.fn b) =
      ∫ x in positiveCoordinates, coordinateDensity x *
        formPairing n p x (frMol n p R.C.χ R.C.η c (CForm.fn a) x) (CForm.fn b x) :=
    localIntegral_eq_setIntegral n p _ _ (Cc.zero_outside hM)
  have h3 := integral_frMol_transpose R.C.χ_smooth R.C.χ_compact R.C.χ_pos R.C.η_smooth
    R.C.η_compact R.C.η_pos hc.ne' (CForm.smooth a) (CForm.smooth b)
  have h4 : l2Form Γ n p (R.trans p hc b) a = ∫ x in positiveCoordinates,
      coordinateDensity x * formPairing n p x (frTr n p R.C.χ R.C.η c (CForm.fn b) x)
        (CForm.fn a x) := h.l2Form_avg hT a
  have h5 : (∫ x in positiveCoordinates, coordinateDensity x *
      formPairing n p x (frTr n p R.C.χ R.C.η c (CForm.fn b) x) (CForm.fn a x)) =
      ∫ x in positiveCoordinates, coordinateDensity x *
        formPairing n p x (CForm.fn a x) (frTr n p R.C.χ R.C.η c (CForm.fn b) x) :=
    setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet (fun x hx => by
      rw [formPairing_symm n p x hx])
  have h6 : localIntegral n p (CForm.fn a) (frTr n p R.C.χ R.C.η c (CForm.fn b)) =
      ∫ x in positiveCoordinates, coordinateDensity x *
        formPairing n p x (CForm.fn a x) (frTr n p R.C.χ R.C.η c (CForm.fn b) x) :=
    localIntegral_eq_setIntegral n p _ _ (fun x hx => CForm.outside a hx)
  exact (inner_incl Γ n p _ _).trans (h1.trans (h2.symm.trans (h3.trans (h6.trans
    (h5.symm.trans (h4.symm.trans ((l2Form_comm _ _).trans (inner_incl Γ n p _ _).symm)))))))

theorem RegData.regFamily_hasTranspose (p : ℕ) : (R.regFamily (n := n) p).HasTranspose := fun j =>
  ⟨R.trans p (c := (j : ℝ) + 1) (by positivity), fun a b =>
    R.inner_reg_trans p (c := (j : ℝ) + 1) (by positivity) a b⟩

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
