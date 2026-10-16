module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Regulariser

@[expose] public section


/-! # General coercivity, Tier B: the regulariser and the differential operators

For the exterior derivative and the codifferential, the regulariser `r_c` has `d r_c` bounded for a
fixed scale, the commutator `d r_c - r_c d` is bounded uniformly in the scale, and on forms supported
over `Q` it tends to zero.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set MeasureTheory Filter Topology TernaryPoly TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian
open scoped ContDiff

variable {Γ : Subgroup RealGL} {n : ℕ} [hΓ : Fact (Admissible Γ)] {Q : Set (OrbitSpace Γ)}

theorem FODatum.mem_Cc {kin kout : ℕ} {K : Set Coordinates} (F : FODatum n kin kout K)
    {g : Coordinates → FormValue n kin} (hg : g ∈ Cc n kin) :
    F.D g ∈ Cc n kout :=
  ⟨F.smooth g hg.1 hg.2.2, hg.2.1.of_isClosed_subset (isClosed_tsupport _) (F.tsupport_sub g),
    (F.tsupport_sub g).trans hg.2.2⟩

/-- A differential operator on equivariant forms, compatible with the average. -/
structure OpData (R : RegData Γ Q) (kin kout : ℕ) where
  F : FODatum n kin kout (tsupport R.C.θ)
  Dform : CForm Γ n kin →ₗ[ℝ] CForm Γ n kout
  hint : ∀ (g : Coordinates → FormValue n kin) (hg : g ∈ Cc n kin),
    Dform (avgForm hΓ.out g hg) = avgForm hΓ.out (F.D g) (F.mem_Cc hg)
  hfn : ∀ (a : CForm Γ n kin) (x : Coordinates), x ∈ positiveCoordinates →
    CForm.fn (Dform a) x = F.D (CForm.fn a) x
  hsupp : ∀ a ∈ SuppIn Q n kin, Dform a ∈ SuppIn Q n kout

theorem norm_incl_le_of_normSq_le {p q : ℕ} {K : ℝ} (hK : 0 ≤ K) (x : CForm Γ n p)
    (y : CForm Γ n q) (h : normSq x ≤ K * normSq y) :
    ‖incl Γ n p x‖ ≤ Real.sqrt K * ‖incl Γ n q y‖ := by
  have e : (Real.sqrt K * ‖incl Γ n q y‖) ^ 2 = K * normSq y :=
    (mul_pow _ _ 2).trans (congrArg₂ (· * ·) (Real.sq_sqrt hK) (norm_incl_sq Γ n q y))
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    ((norm_incl_sq Γ n p x).trans_le (h.trans_eq e.symm))

theorem aux_chain5 {x w c1 c2 w3 y Nη A1 A2 A3 N3 : ℝ} (hN : 0 ≤ Nη) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hA3 : 0 ≤ A3) (h1 : x ≤ Nη * w) (h2 : w ≤ A1 * c1) (h3 : c1 ≤ A2 * c2) (h4 : c2 ≤ A3 * w3)
    (h5 : w3 ≤ N3 * y) : x ≤ Nη * A1 * A2 * A3 * N3 * y := by
  have g1 : c2 ≤ A3 * (N3 * y) := h4.trans (mul_le_mul_of_nonneg_left h5 hA3)
  have g2 : c1 ≤ A2 * (A3 * (N3 * y)) := h3.trans (mul_le_mul_of_nonneg_left g1 hA2)
  have g3 : w ≤ A1 * (A2 * (A3 * (N3 * y))) := h2.trans (mul_le_mul_of_nonneg_left g2 hA1)
  have g4 : x ≤ Nη * (A1 * (A2 * (A3 * (N3 * y)))) := h1.trans (mul_le_mul_of_nonneg_left g3 hN)
  calc x ≤ Nη * (A1 * (A2 * (A3 * (N3 * y)))) := g4
    _ = Nη * A1 * A2 * A3 * N3 * y := by ring

theorem RegData.exists_N3θ (R : RegData Γ Q) (p : ℕ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ a : CForm Γ n p, wL2 (fun y => R.C.θ y • CForm.fn a y) ≤ N * normSq a := by
  have hΛ := exists_abs_bound R.C.θ_smooth.continuous R.C.θ_compact
  exact wL2_cut_le (Γ := Γ) (n := n) (k := p) R.C.θ_smooth R.C.θ_compact R.C.θ_pos hΛ.choose_spec

omit hΓ in
theorem RegData.exists_Aθ (R : RegData Γ Q) (p : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ g : Coordinates → FormValue n p, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ tsupport R.C.θ → wL2 g ≤ A * compL2 g ∧ compL2 g ≤ A * wL2 g :=
  exists_wL2_comp n p R.C.θ_compact.isCompact R.C.θ_pos

section Ops

variable {R : RegData Γ Q} {kin kout : ℕ} (O : OpData R kin kout)

/-- The fixed-scale bound for `D r_c`. -/
theorem OpData.exists_normSq_fixed_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : CForm Γ n kin,
      normSq (O.Dform (R.reg kin hc a)) ≤ K * normSq a := by
  have h := hΓ.out
  have hfix := exists_compL2_D_frMol_le R.C O.F hc
  have hK := R.C.η_compact.isCompact
  have hcomp := exists_wL2_comp n kout hK R.C.η_pos
  have hc2 := R.exists_Ac (n := n) kin
  have h3 := R.exists_N3 (n := n) kin
  have hNη : 0 ≤ ((h.overlap_finite hK R.C.η_pos).toFinset.card : ℝ) := Nat.cast_nonneg _
  refine ⟨((h.overlap_finite hK R.C.η_pos).toFinset.card : ℝ) * hcomp.choose * hfix.choose *
    hc2.choose * h3.choose, mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hNη
      hcomp.choose_spec.1) hfix.choose_spec.1) hc2.choose_spec.1) h3.choose_spec.1, fun a => ?_⟩
  have hM := (R.Mol kin hc a).2
  have hg1 := O.F.mem_Cc hM
  have hsub : tsupport (O.F.D (frMol n kin R.C.χ R.C.η c (CForm.fn a))) ⊆ tsupport R.C.η :=
    (O.F.tsupport_sub _).trans (tsupport_frMol_subset R.C.χ R.C.η c _)
  have hDa : O.Dform (R.reg kin hc a) = avgForm h (O.F.D (frMol n kin R.C.χ R.C.η c (CForm.fn a)))
      hg1 := O.hint _ hM
  have e1 : normSq (O.Dform (R.reg kin hc a)) ≤ ((h.overlap_finite hK R.C.η_pos).toFinset.card : ℝ) *
      wL2 (O.F.D (frMol n kin R.C.χ R.C.η c (CForm.fn a))) := by
    rw [hDa]
    exact h.normSq_avgForm_le_of_subset hg1 hK R.C.η_pos hsub
  have e2 := (hcomp.choose_spec.2 _ hg1.1 hg1.2.1 hsub).1
  have e3 := hfix.choose_spec.2 (CForm.smooth a)
  have hcg := R.cutMem kin a
  have e4 := (hc2.choose_spec.2 _ hcg.1 hcg.2.1 (tsupport_cut_subset R.C.χ _)).2
  have e5 := h3.choose_spec.2 a
  exact aux_chain5 hNη hcomp.choose_spec.1 hfix.choose_spec.1 hc2.choose_spec.1 e1 e2 e3 e4 e5

theorem sub_eq_add_neg_smul' {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : V) :
    a - b = a + (-1 : ℝ) • b := by
  rw [neg_one_smul]
  exact sub_eq_add_neg a b

theorem OpData.D_eq_on (a : CForm Γ n kin) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    O.F.D (CForm.fn a) x = CForm.fn (O.Dform a) x := (O.hfn a x hx).symm

theorem OpData.contDiffOn_D (a : CForm Γ n kin) :
    ContDiffOn ℝ ∞ (O.F.D (CForm.fn a)) positiveCoordinates :=
  (CForm.smooth (O.Dform a)).congr (fun _ hx => O.D_eq_on a hx)

theorem OpData.frMol_D_eq (a : CForm Γ n kin) (c : ℝ) :
    frMol n kout R.C.χ R.C.η c (O.F.D (CForm.fn a)) =
      frMol n kout R.C.χ R.C.η c (CForm.fn (O.Dform a)) :=
  frMol_congr_on c (fun _ hy => O.D_eq_on a (R.C.χ_pos hy))

/-- `F.D (frMol c f_a) - frMol c (F.D f_a)` as a compactly supported smooth form. -/
def OpData.diffg (a : CForm Γ n kin) {c : ℝ} (hc : 0 < c) : Cc n kout :=
  (⟨O.F.D (frMol n kin R.C.χ R.C.η c (CForm.fn a)), O.F.mem_Cc (R.Mol kin hc a).2⟩ : Cc n kout) -
    R.Mol kout hc (O.Dform a)

theorem OpData.diffg_fun (a : CForm Γ n kin) {c : ℝ} (hc : 0 < c) :
    (O.diffg a hc).1 = fun x => O.F.D (frMol n kin R.C.χ R.C.η c (CForm.fn a)) x -
      frMol n kout R.C.χ R.C.η c (O.F.D (CForm.fn a)) x := by
  funext x
  exact congrArg (fun G : Coordinates → FormValue n kout =>
    O.F.D (frMol n kin R.C.χ R.C.η c (CForm.fn a)) x - G x) (O.frMol_D_eq a c).symm

theorem OpData.comm_eq_avg (a : CForm Γ n kin) {c : ℝ} (hc : 0 < c) :
    O.Dform (R.reg kin hc a) + (-1 : ℝ) • R.reg kout hc (O.Dform a) =
      avg hΓ.out (O.diffg a hc) := by
  have e1 : O.Dform (R.reg kin hc a) =
      avg hΓ.out (⟨O.F.D (frMol n kin R.C.χ R.C.η c (CForm.fn a)),
        O.F.mem_Cc (R.Mol kin hc a).2⟩ : Cc n kout) := O.hint _ (R.Mol kin hc a).2
  have e2 := map_sub (avg hΓ.out)
    (⟨O.F.D (frMol n kin R.C.χ R.C.η c (CForm.fn a)), O.F.mem_Cc (R.Mol kin hc a).2⟩ : Cc n kout)
    (R.Mol kout hc (O.Dform a))
  refine Eq.trans ?_ e2.symm
  exact (congrArg (fun z : CForm Γ n kout => z + (-1 : ℝ) • R.reg kout hc (O.Dform a)) e1).trans
    (sub_eq_add_neg_smul' _ _).symm

/-- The scale-uniform bound for the commutator of `D` with the regulariser. -/
theorem OpData.exists_normSq_comm_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {c : ℝ} (hc : 0 < c) (a : CForm Γ n kin),
      normSq (O.Dform (R.reg kin hc a) + (-1 : ℝ) • R.reg kout hc (O.Dform a)) ≤
        K * normSq a := by
  have h := hΓ.out
  have hcm := exists_compL2_commutator_le R.C O.F
  have hK := R.C.η_compact.isCompact
  have hcomp := exists_wL2_comp n kout hK R.C.η_pos
  have hθ := R.exists_Aθ (n := n) kin
  have h3 := R.exists_N3θ (n := n) kin
  have hNη : 0 ≤ ((h.overlap_finite hK R.C.η_pos).toFinset.card : ℝ) := Nat.cast_nonneg _
  refine ⟨((h.overlap_finite hK R.C.η_pos).toFinset.card : ℝ) * hcomp.choose * hcm.choose *
    hθ.choose * h3.choose, mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hNη
      hcomp.choose_spec.1) hcm.choose_spec.1) hθ.choose_spec.1) h3.choose_spec.1,
    fun {c} hc a => ?_⟩
  have hgf := O.diffg a hc
  have hd := (O.diffg a hc).2
  have hsub : tsupport (O.diffg a hc).1 ⊆ tsupport R.C.η := by
    refine (tsupport_sub _ _).trans (union_subset ?_ ?_)
    · exact (O.F.tsupport_sub _).trans (tsupport_frMol_subset R.C.χ R.C.η c _)
    · exact (R.Mol kout hc (O.Dform a)).2.2.2 |> fun _ => (tsupport_frMol_subset R.C.χ R.C.η c _)
  have e1 : normSq (avg h (O.diffg a hc)) ≤ ((h.overlap_finite hK R.C.η_pos).toFinset.card : ℝ) *
      wL2 (O.diffg a hc).1 := h.normSq_avgForm_le_of_subset hd hK R.C.η_pos hsub
  have e2 := (hcomp.choose_spec.2 _ hd.1 hd.2.1 hsub).1
  have e3 : compL2 (O.diffg a hc).1 ≤ hcm.choose * compL2 (fun y => R.C.θ y • CForm.fn a y) := by
    rw [O.diffg_fun a hc]
    exact hcm.choose_spec.2 hc (CForm.smooth a)
  have hcg := cut_mem_Cc R.C.θ_smooth R.C.θ_compact R.C.θ_pos (CForm.smooth a)
  have e4 := (hθ.choose_spec.2 _ hcg.1 hcg.2.1 (tsupport_cut_subset R.C.θ _)).2
  have e5 := h3.choose_spec.2 a
  rw [O.comm_eq_avg a hc]
  exact aux_chain5 hNη hcomp.choose_spec.1 hcm.choose_spec.1 hθ.choose_spec.1 e1 e2 e3 e4 e5

/-- The differential of the cutoff, as a compactly supported smooth form. -/
def OpData.X2 (a : CForm Γ n kin) : Cc n kout :=
  ⟨O.F.D (fun y => R.C.χ y • CForm.fn a y), O.F.mem_Cc (R.cutMem kin a)⟩

/-- The cutoff of the differential, as a compactly supported smooth form. -/
def OpData.Y2 (a : CForm Γ n kin) : Cc n kout :=
  ⟨fun y => R.C.χ y • CForm.fn (O.Dform a) y, R.cutMem kout (O.Dform a)⟩

theorem OpData.chi_D_eq (a : CForm Γ n kin) :
    (fun y => R.C.χ y • O.F.D (CForm.fn a) y) = fun y => R.C.χ y • CForm.fn (O.Dform a) y := by
  funext y
  by_cases hy : y ∈ tsupport R.C.χ
  · exact congrArg (fun z : FormValue n kout => R.C.χ y • z) (O.D_eq_on a (R.C.χ_pos hy))
  · have h0 : R.C.χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have e1 : R.C.χ y • O.F.D (CForm.fn a) y = 0 :=
      (congrArg (fun r : ℝ => r • O.F.D (CForm.fn a) y) h0).trans (zero_smul_fv _)
    have e2 : R.C.χ y • CForm.fn (O.Dform a) y = 0 :=
      (congrArg (fun r : ℝ => r • CForm.fn (O.Dform a) y) h0).trans (zero_smul_fv _)
    exact e1.trans e2.symm

theorem OpData.avg_X2_sub_Y2 {a : CForm Γ n kin} (ha : a ∈ SuppIn Q n kin) :
    avg hΓ.out (O.X2 a - O.Y2 a) = 0 := by
  have e1 : avg hΓ.out (O.X2 a) = O.Dform a := by
    have h1 := O.hint (fun y => R.C.χ y • CForm.fn a y) (R.cutMem kin a)
    exact h1.symm.trans (congrArg O.Dform (R.avg_cut_eq_self kin ha))
  have e2 : avg hΓ.out (O.Y2 a) = O.Dform a := R.avg_cut_eq_self kout (O.hsupp a ha)
  exact (map_sub (avg hΓ.out) (O.X2 a) (O.Y2 a)).trans
    ((congrArg₂ (· - ·) e1 e2).trans (sub_self _))

/-- The defect of the commutator from its symbol, as a compactly supported smooth form. -/
def OpData.commCc (a : CForm Γ n kin) {c : ℝ} (hc : 0 < c) : Cc n kout :=
  O.diffg a hc - (O.X2 a - O.Y2 a)

theorem OpData.commCc_fun (a : CForm Γ n kin) {c : ℝ} (hc : 0 < c) :
    (O.commCc a hc).1 = commFun R.C O.F c (CForm.fn a) := by
  funext x
  have e1 : O.F.D (fun y => R.C.η y • (R.C.χ y • CForm.fn a y)) =
      O.F.D (fun y => R.C.χ y • CForm.fn a y) := congrArg O.F.D (R.eta_cut (CForm.fn a))
  have e2 : R.C.η x • (R.C.χ x • O.F.D (CForm.fn a) x) = R.C.χ x • CForm.fn (O.Dform a) x :=
    (congrFun (R.eta_cut (O.F.D (CForm.fn a))) x).trans (congrFun (O.chi_D_eq a) x)
  change ((O.diffg a hc).1 x) - ((O.X2 a).1 x - (O.Y2 a).1 x) = _
  rw [O.diffg_fun a hc]
  unfold commFun
  exact congrArg₂ (· - ·) rfl (congrArg₂ (· - ·) (congrFun e1 x).symm e2.symm)

theorem OpData.comm_eq_avg_commCc {a : CForm Γ n kin} (ha : a ∈ SuppIn Q n kin) {c : ℝ}
    (hc : 0 < c) :
    O.Dform (R.reg kin hc a) + (-1 : ℝ) • R.reg kout hc (O.Dform a) = avg hΓ.out (O.commCc a hc) := by
  have e := map_sub (avg hΓ.out) (O.diffg a hc) (O.X2 a - O.Y2 a)
  rw [O.comm_eq_avg a hc]
  exact (sub_zero (avg hΓ.out (O.diffg a hc))).symm.trans
    ((congrArg (fun z => avg hΓ.out (O.diffg a hc) - z) (O.avg_X2_sub_Y2 ha).symm).trans e.symm)

theorem OpData.comm_tendsto {a : CForm Γ n kin} (ha : a ∈ SuppIn Q n kin) :
    Tendsto (fun j : ℕ => incl Γ n kout (O.Dform (R.regSeq kin j a) +
      (-1 : ℝ) • R.regSeq kout j (O.Dform a))) atTop (𝓝 0) := by
  have h := hΓ.out
  apply tendsto_of_sq_norm_tendsto_zero
  have hle : ∀ j : ℕ, ‖incl Γ n kout (O.Dform (R.regSeq kin j a) +
      (-1 : ℝ) • R.regSeq kout j (O.Dform a)) - 0‖ ^ 2 ≤
      ((h.overlap_finite R.C.η_compact.isCompact R.C.η_pos).toFinset.card : ℝ) *
        wL2 (commFun R.C O.F ((j : ℝ) + 1) (CForm.fn a)) := by
    intro j
    have hc : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hsub : tsupport (O.commCc a hc).1 ⊆ tsupport R.C.η := by
      refine (tsupport_sub _ _).trans (union_subset ?_ ?_)
      · refine (tsupport_sub _ _).trans (union_subset ?_ ?_)
        · exact (O.F.tsupport_sub _).trans (tsupport_frMol_subset R.C.χ R.C.η _ _)
        · exact tsupport_frMol_subset R.C.χ R.C.η _ _
      · refine (tsupport_sub _ _).trans (union_subset ?_ ?_)
        · exact ((O.F.tsupport_sub _).trans (tsupport_cut_subset R.C.χ _)).trans R.tsupport_χ_sub_η
        · exact (tsupport_cut_subset R.C.χ _).trans R.tsupport_χ_sub_η
    have e1 := h.normSq_avgForm_le_of_subset (O.commCc a hc).2 R.C.η_compact.isCompact R.C.η_pos hsub
    have e2 : wL2 (O.commCc a hc).1 = wL2 (commFun R.C O.F ((j : ℝ) + 1) (CForm.fn a)) :=
      congrArg wL2 (O.commCc_fun a hc)
    have e3 : incl Γ n kout (O.Dform (R.regSeq kin j a) +
        (-1 : ℝ) • R.regSeq kout j (O.Dform a)) - 0 = incl Γ n kout (avg h (O.commCc a hc)) :=
      (sub_zero _).trans (congrArg (incl Γ n kout) (O.comm_eq_avg_commCc ha hc))
    exact (congrArg (fun z : Hilbert Γ n kout => ‖z‖ ^ 2) e3).trans_le
      ((norm_incl_sq Γ n kout _).trans_le (e1.trans_eq (congrArg _ e2)))
  have hlim : Tendsto (fun j : ℕ => ((h.overlap_finite R.C.η_compact.isCompact
      R.C.η_pos).toFinset.card : ℝ) * wL2 (commFun R.C O.F ((j : ℝ) + 1) (CForm.fn a))) atTop
      (𝓝 0) := by
    have h1 := (commutator_tendsto R.C O.F (CForm.smooth a)).comp tendsto_natCast_add_one_atTop
    have h2 := h1.const_mul ((h.overlap_finite R.C.η_compact.isCompact
      R.C.η_pos).toFinset.card : ℝ)
    rw [mul_zero] at h2
    exact h2
  exact squeeze_zero' (Eventually.of_forall fun j => sq_nonneg _) (Eventually.of_forall hle) hlim

end Ops

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
