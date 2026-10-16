module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Measure.Quotient
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalAdjoint
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section


/-!
# General coercivity: smooth cutoffs adapted to an admissible group

For a compact subset `Q` of the orbit space we construct a smooth, nonnegative, compactly supported
function `φ` on the coordinates `ℝ⁵` (with support in `positiveCoordinates`) whose `Γ`-translates sum
to one on an open neighbourhood of the lift of `Q`, and such that the sum of translates is locally
finite.  Such a `φ` is the partition of unity used to unfold integrals over the orbit space.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set Topology TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
open TernaryPoly.SymmetricSpaceCovering TernaryPoly.CompactCoordinateIntegration
open scoped ContDiff
open Function (support)

variable {Γ : Subgroup RealGL}

/-- A smooth nonnegative compactly supported function in `positiveCoordinates` exceeding `1/2` on a
given compact set. -/
theorem exists_bump_sum {C : Set Coordinates} (hC : IsCompact C) (hCU : C ⊆ positiveCoordinates) :
    ∃ χ : Coordinates → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ positiveCoordinates ∧ (∀ x, 0 ≤ χ x) ∧ ∀ x ∈ C, 1 / 2 < χ x := by
  have hb : ∀ x ∈ C, ∃ f : Coordinates → ℝ, tsupport f ⊆ positiveCoordinates ∧
      HasCompactSupport f ∧ ContDiff ℝ ∞ f ∧ range f ⊆ Icc 0 1 ∧ f x = 1 :=
    fun x hx => exists_contDiff_tsupport_subset (isOpen_positiveCoordinates.mem_nhds (hCU hx))
  choose! f hfs hfc hfd hfr hf1 using hb
  obtain ⟨s, hsC, hs⟩ := hC.elim_nhds_subcover (fun x => {y | 1 / 2 < f x y})
    (fun x hx => (isOpen_lt continuous_const (hfd x hx).continuous).mem_nhds
      (by show (1 : ℝ) / 2 < f x x; rw [hf1 x hx]; norm_num))
  have hnn : ∀ x ∈ C, ∀ y, 0 ≤ f x y := fun x hx y => (hfr x hx (mem_range_self y)).1
  let T : Set Coordinates := ⋃ x ∈ s, tsupport (f x)
  have hT : IsCompact T := s.isCompact_biUnion fun x hx => hfc x (hsC x hx)
  have hsupp : support (fun y => ∑ x ∈ s, f x y) ⊆ T := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    exact mem_iUnion₂.mpr ⟨x, hx, subset_tsupport _ hxy⟩
  have htsub : tsupport (fun y => ∑ x ∈ s, f x y) ⊆ T := closure_minimal hsupp hT.isClosed
  refine ⟨fun y => ∑ x ∈ s, f x y, ?_, hT.of_isClosed_subset (isClosed_tsupport _) htsub,
    htsub.trans (iUnion₂_subset fun x hx => hfs x (hsC x hx)),
    fun y => Finset.sum_nonneg fun x hx => hnn x (hsC x hx) y, ?_⟩
  · exact ContDiff.sum fun x hx => hfd x (hsC x hx)
  · intro x hx
    obtain ⟨z, hz, hlt⟩ := mem_iUnion₂.mp (hs hx)
    exact lt_of_lt_of_le hlt
      (Finset.single_le_sum (f := fun w => f w x) (fun w hw => hnn w (hsC w hw) x) hz)

/-- Local finiteness of the translates of a compactly supported function. -/
theorem Admissible.cutoff_locallyFinite (h : Admissible Γ) {χ : Coordinates → ℝ}
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ positiveCoordinates) :
    ∀ x ∈ positiveCoordinates, ∃ N ∈ 𝓝 x, N ⊆ positiveCoordinates ∧
      {γ : Γ | ∃ y ∈ N, χ (coordinateAction (γ : RealGL) y) ≠ 0}.Finite := by
  intro x hx
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds (coordinateChart.symm x)
  have hD : IsCompact (coordinateChart.symm '' tsupport χ) :=
    hc.image_of_continuousOn (coordinateChart.continuousOn_symm.mono (fun y hy => by
      simpa using hs hy))
  have hxs : x ∈ coordinateChart.target := by simpa using hx
  have hNn : coordinateChart '' N ∈ 𝓝 x := by
    have := coordinateChart.image_mem_nhds (x := coordinateChart.symm x) (by simp)
      hN
    rwa [coordinateChart.right_inv hxs] at this
  refine ⟨coordinateChart '' N, hNn, ?_, ?_⟩
  · rintro _ ⟨S, -, rfl⟩
    exact extract_mem S
  · refine (h.transporters N _ hNc hD).subset ?_
    rintro γ ⟨y, ⟨S, hS, rfl⟩, hne⟩
    have hmem : coordinateAction (γ : RealGL) (coordinateChart S) = coordinateChart (γ • S) :=
      (coordinateChart_act (γ : RealGL) S).symm
    rw [hmem] at hne
    refine ⟨γ • S, ⟨S, hS, rfl⟩, ?_⟩
    exact ⟨coordinateChart (γ • S), subset_tsupport _ hne,
      coordinateChart.left_inv (by simp)⟩

/-- The sum of the `Γ`-translates of a function on the coordinates. -/
def cutoffSum (Γ : Subgroup RealGL) (χ : Coordinates → ℝ) (x : Coordinates) : ℝ :=
  ∑ᶠ γ : Γ, χ (coordinateAction (γ : RealGL) x)

theorem Admissible.cutoffSum_finite (h : Admissible Γ) {χ : Coordinates → ℝ}
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ positiveCoordinates) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    (support fun γ : Γ => χ (coordinateAction (γ : RealGL) x)).Finite := by
  obtain ⟨N, hN, -, hfin⟩ := h.cutoff_locallyFinite hc hs x hx
  exact hfin.subset fun γ hγ => ⟨x, mem_of_mem_nhds hN, hγ⟩

theorem Admissible.contDiffOn_cutoffSum (h : Admissible Γ) {χ : Coordinates → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ positiveCoordinates) :
    ContDiffOn ℝ ∞ (cutoffSum Γ χ) positiveCoordinates := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨N, hN, hNp, hfin⟩ := h.cutoff_locallyFinite hc hs x hx
  refine ⟨interior N, isOpen_interior, mem_interior_iff_mem_nhds.mpr hN, ?_⟩
  have hsum : ContDiffOn ℝ ∞
      (fun y => ∑ γ ∈ hfin.toFinset, χ (coordinateAction (γ : RealGL) y))
      (positiveCoordinates ∩ interior N) :=
    ContDiffOn.sum fun γ _ =>
      hχ.comp_contDiffOn ((contDiffOn_coordinateAction (γ : RealGL)).mono inter_subset_left)
  refine hsum.congr fun y hy => ?_
  unfold cutoffSum
  apply finsum_eq_sum_of_support_subset
  intro γ hγ
  exact hfin.mem_toFinset.mpr ⟨y, interior_subset hy.2, hγ⟩

theorem cutoffSum_action {χ : Coordinates → ℝ} (γ : Γ) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    cutoffSum Γ χ (coordinateAction (γ : RealGL) x) = cutoffSum Γ χ x := by
  unfold cutoffSum
  calc ∑ᶠ δ : Γ, χ (coordinateAction (δ : RealGL) (coordinateAction (γ : RealGL) x))
      = ∑ᶠ δ : Γ, (fun ε : Γ => χ (coordinateAction (ε : RealGL) x)) (Equiv.mulRight γ δ) :=
        finsum_congr fun δ => by
          rw [← coordinateAction_mul _ _ hx]
          rfl
    _ = ∑ᶠ δ : Γ, χ (coordinateAction (δ : RealGL) x) :=
        finsum_comp_equiv (f := fun ε : Γ => χ (coordinateAction (ε : RealGL) x)) (Equiv.mulRight γ)

/-- A smooth reciprocal that is exactly `1 / t` for `t ≥ 1/4` and vanishes for `t ≤ 1/8`. -/
def recipCut (t : ℝ) : ℝ := Real.smoothTransition (8 * t - 1) * t⁻¹

theorem contDiff_recipCut : ContDiff ℝ ∞ recipCut := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < 1 / 8
  · have : recipCut =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have : 8 * s - 1 ≤ 0 := by simp only [mem_Iio] at hs; linarith
      simp [recipCut, Real.smoothTransition.zero_of_nonpos this]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq this
  · have hpos : t ≠ 0 := by
      intro h0
      apply ht
      rw [h0]
      norm_num
    exact ((Real.smoothTransition.contDiff.comp (by fun_prop : ContDiff ℝ ∞ fun s : ℝ => 8 * s - 1)).contDiffAt).mul
      (contDiffAt_inv ℝ hpos)

theorem recipCut_nonneg (t : ℝ) : 0 ≤ recipCut t := by
  by_cases ht : t ≤ 0
  · have : 8 * t - 1 ≤ 0 := by linarith
    simp [recipCut, Real.smoothTransition.zero_of_nonpos this]
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (inv_nonneg.mpr (not_le.mp ht).le)

theorem mul_recipCut {t : ℝ} (ht : 1 / 4 ≤ t) : t * recipCut t = 1 := by
  have h1 : 1 ≤ 8 * t - 1 := by linarith
  have h0 : t ≠ 0 := by positivity
  rw [recipCut, Real.smoothTransition.one_of_one_le h1, one_mul, mul_inv_cancel₀ h0]

/-- The cutoff data attached to a compact subset `Q` of the orbit space. -/
structure CutoffData (Γ : Subgroup RealGL) (Q : Set (OrbitSpace Γ)) (φ : Coordinates → ℝ) :
    Prop where
  smooth : ContDiff ℝ ∞ φ
  compactSupport : HasCompactSupport φ
  tsupport_subset : tsupport φ ⊆ positiveCoordinates
  nonneg : ∀ x, 0 ≤ φ x
  locallyFinite : ∀ x ∈ positiveCoordinates, ∃ N ∈ 𝓝 x, N ⊆ positiveCoordinates ∧
    {γ : Γ | ∃ y ∈ N, φ (coordinateAction (γ : RealGL) y) ≠ 0}.Finite
  partition : ∃ W : Set Coordinates, IsOpen W ∧ W ⊆ positiveCoordinates ∧
    (∀ x ∈ positiveCoordinates, coordProj Γ x ∈ Q → x ∈ W) ∧
    ∀ x ∈ W, ∑ᶠ γ : Γ, φ (coordinateAction (γ : RealGL) x) = 1

/-- Every compact subset of the orbit space of an admissible group admits a cutoff partition. -/
theorem Admissible.exists_cutoff (h : Admissible Γ) {Q : Set (OrbitSpace Γ)} (hQ : IsCompact Q) :
    ∃ φ : Coordinates → ℝ, CutoffData Γ Q φ := by
  obtain ⟨K, hK, hQK⟩ := h.exists_compact_lift hQ
  have hC : IsCompact (coordinateChart '' K) := hK.image coordinateEmbedding.continuous
  have hCp : coordinateChart '' K ⊆ positiveCoordinates := by
    rintro _ ⟨S, -, rfl⟩
    exact extract_mem S
  obtain ⟨χ, hχd, hχc, hχs, hχ0, hχC⟩ := exists_bump_sum hC hCp
  have hΨd := h.contDiffOn_cutoffSum hχd hχc hχs
  have hΨfin := fun {x} (hx : x ∈ positiveCoordinates) => h.cutoffSum_finite hχc hχs hx
  have hΨ0 : ∀ x, 0 ≤ cutoffSum Γ χ x := fun x => finsum_nonneg fun γ => hχ0 _
  have hsupp : support (fun x => χ x * recipCut (cutoffSum Γ χ x)) ⊆ support χ :=
    fun y hy => left_ne_zero_of_mul hy
  have htsub : tsupport (fun x => χ x * recipCut (cutoffSum Γ χ x)) ⊆ positiveCoordinates :=
    (closure_mono hsupp).trans hχs
  have hOn : ContDiffOn ℝ ∞ (fun x => χ x * recipCut (cutoffSum Γ χ x)) positiveCoordinates :=
    hχd.contDiffOn.mul (contDiff_recipCut.comp_contDiffOn hΨd)
  refine ⟨fun x => χ x * recipCut (cutoffSum Γ χ x), ?_⟩
  refine ⟨contDiff_of_tsupport_subset isOpen_positiveCoordinates hOn htsub,
    hχc.mono' (hsupp.trans (subset_tsupport _)), htsub,
    fun x => mul_nonneg (hχ0 x) (recipCut_nonneg _), ?_, ?_⟩
  · intro x hx
    obtain ⟨N, hN, hNp, hfin⟩ := h.cutoff_locallyFinite hχc hχs x hx
    refine ⟨N, hN, hNp, hfin.subset ?_⟩
    rintro γ ⟨y, hy, hne⟩
    exact ⟨y, hy, left_ne_zero_of_mul hne⟩
  · refine ⟨positiveCoordinates ∩ cutoffSum Γ χ ⁻¹' Ioi (1 / 4),
      hΨd.continuousOn.isOpen_inter_preimage isOpen_positiveCoordinates isOpen_Ioi,
      inter_subset_left, ?_, ?_⟩
    · intro x hx hxQ
      refine ⟨hx, ?_⟩
      obtain ⟨S', hS'K, hS'⟩ := hQK hxQ
      obtain ⟨γ, hγ⟩ := proj_eq_iff.mp hS'
      have hxeq : x = coordinateAction (γ : RealGL) (coordinateChart S') := by
        rw [← coordinateChart_act]
        change x = coordinateChart (γ • S')
        rw [hγ, coordinateChart.right_inv (by simpa using hx)]
      have hy : coordinateChart S' ∈ positiveCoordinates := extract_mem S'
      have hΨx : cutoffSum Γ χ x = cutoffSum Γ χ (coordinateChart S') := by
        rw [hxeq]
        exact cutoffSum_action γ hy
      have hle : χ (coordinateChart S') ≤ cutoffSum Γ χ (coordinateChart S') := by
        have h1 : χ (coordinateAction ((1 : Γ) : RealGL) (coordinateChart S')) =
            χ (coordinateChart S') := by
          rw [Subgroup.coe_one, coordinateAction_one hy]
        have := single_le_finsum (1 : Γ) (hΨfin hy) (fun γ => hχ0 _)
        rw [h1] at this
        exact this
      show 1 / 4 < cutoffSum Γ χ x
      rw [hΨx]
      have := hχC _ ⟨S', hS'K, rfl⟩
      linarith
    · rintro x ⟨hx, hΨ⟩
      have hΨ' : 1 / 4 < cutoffSum Γ χ x := hΨ
      have hterm : ∀ γ : Γ, χ (coordinateAction (γ : RealGL) x) *
          recipCut (cutoffSum Γ χ (coordinateAction (γ : RealGL) x)) =
          χ (coordinateAction (γ : RealGL) x) * recipCut (cutoffSum Γ χ x) := fun γ => by
        rw [cutoffSum_action γ hx]
      calc ∑ᶠ γ : Γ, χ (coordinateAction (γ : RealGL) x) *
            recipCut (cutoffSum Γ χ (coordinateAction (γ : RealGL) x))
          = ∑ᶠ γ : Γ, χ (coordinateAction (γ : RealGL) x) * recipCut (cutoffSum Γ χ x) :=
            finsum_congr hterm
        _ = cutoffSum Γ χ x * recipCut (cutoffSum Γ χ x) := (finsum_mul _ _).symm
        _ = 1 := mul_recipCut hΨ'.le

/-- The translates of a cutoff, evaluated in the chart, sum to one over the lift of `Q`. -/
theorem CutoffData.tsum_eq_one {Q : Set (OrbitSpace Γ)} {φ : Coordinates → ℝ}
    (hφ : CutoffData Γ Q φ) {S : Space} (hS : proj Γ S ∈ Q) :
    ∑' γ : Γ, φ (coordinateChart (γ • S)) = 1 := by
  obtain ⟨W, -, -, hW, hsum⟩ := hφ.partition
  have hx : coordinateChart S ∈ positiveCoordinates := extract_mem S
  have hmemW : coordinateChart S ∈ W := hW _ hx (by rwa [coordProj_chart])
  have hfin : (support fun γ : Γ => φ (coordinateAction (γ : RealGL) (coordinateChart S))).Finite := by
    obtain ⟨N, hN, -, hfin⟩ := hφ.locallyFinite _ hx
    exact hfin.subset fun γ hγ => ⟨_, mem_of_mem_nhds hN, hγ⟩
  have : ∀ γ : Γ, φ (coordinateChart (γ • S)) = φ (coordinateAction (γ : RealGL) (coordinateChart S)) :=
    fun γ => by rw [← coordinateChart_act]; rfl
  simp only [this]
  rw [tsum_eq_finsum hfin]
  exact hsum _ hmemW

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
