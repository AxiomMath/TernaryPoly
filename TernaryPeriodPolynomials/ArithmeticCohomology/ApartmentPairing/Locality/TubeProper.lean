module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.SheetGeometry
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ThomY

@[expose] public section


/-!
# Lemma 3.3, G3: a thin tube around the flat with finitely many sheets over every compact

`tube_proper` produces a continuous positive radius `ρ'` below a given bound that stays below `‖π‖` on a
prescribed closed set `N` missing the flat, such that the closed tube `{‖π‖ ≤ ρ'}` meets the level six
translates of every compact set in finitely many sheets.  The point is that the tube does not need to
be uniformly thin: far out along the flat the radius has to decay so that no compact set sees
infinitely many of its translates; the radius is chosen below `‖π‖` on the closed set of points that lie
in a translate of the `n`th compact and have `‖t‖ ≥ Tₙ`, where `Tₙ` bounds the flat points of the
(finitely many) translates of the `n`th compact that meet the flat.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

/-- Only finitely many level six elements carry a point of a compact set into another compact set. -/
theorem transporter_finite_six (A L : Set Space) (hA : IsCompact A) (hL : IsCompact L) :
    {g : principalSix | ∃ S ∈ A, g • S ∈ L}.Finite := by
  have h := compact_transporter_finite A L hA hL
  refine (h.preimage (Subtype.val_injective.injOn)).subset ?_
  rintro g ⟨S, hS, hgS⟩
  exact ⟨S, hS, hgS⟩

theorem continuous_smul_six (g : principalSix) : Continuous fun S : Space => g • S :=
  continuous_act _

theorem isClosed_smul_set (g : principalSix) {Z : Set Space} (hZ : IsClosed Z) : IsClosed (g • Z) := by
  have : g • Z = (fun S : Space => g⁻¹ • S) ⁻¹' Z := by
    ext S
    exact Set.mem_smul_set_iff_inv_smul_mem
  rw [this]
  exact hZ.preimage (continuous_smul_six g⁻¹)

/-- A locally finite family of translates of a closed set has closed union (over any index set). -/
theorem isClosed_biUnion_smul (Z : Set Space) (hZ : IsClosed Z)
    (hfin : ∀ L : Set Space, IsCompact L → {g : principalSix | ((g • Z) ∩ L).Nonempty}.Finite)
    (P : Set principalSix) : IsClosed (⋃ g ∈ P, g • Z) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨L, hLc, hLx⟩ : ∃ L : Set Space, IsCompact L ∧ L ∈ nhds x := by
    refine ⟨coordHomeo.symm '' (Metric.closedBall (coordHomeo x) 1), ?_, ?_⟩
    · exact (isCompact_closedBall _ _).image coordHomeo.symm.continuous
    · have : coordHomeo.symm '' (Metric.closedBall (coordHomeo x) 1) =
          coordHomeo ⁻¹' (Metric.closedBall (coordHomeo x) 1) := by
        ext S
        constructor
        · rintro ⟨q, hq, rfl⟩; simpa using hq
        · intro hS; exact ⟨coordHomeo S, hS, by simp⟩
      rw [this]
      exact coordHomeo.continuous.continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ one_pos)
  have hfinL := hfin L hLc
  let C : Set Space := ⋃ g ∈ {g : principalSix | ((g • Z) ∩ L).Nonempty} ∩ P, g • Z
  have hCc : IsClosed C := by
    refine (hfinL.inter_of_left P).isClosed_biUnion fun g _ => isClosed_smul_set g hZ
  have hxC : x ∉ C := by
    intro h
    simp only [C, Set.mem_iUnion] at h
    obtain ⟨g, ⟨_, hgP⟩, hg⟩ := h
    exact hx (Set.mem_iUnion₂.mpr ⟨g, hgP, hg⟩)
  have hopen : IsOpen Cᶜ := hCc.isOpen_compl
  refine Filter.mem_of_superset (Filter.inter_mem (hopen.mem_nhds hxC) hLx) ?_
  rintro y ⟨hyC, hyL⟩ hy
  obtain ⟨g, hgP, hg⟩ := Set.mem_iUnion₂.mp hy
  apply hyC
  simp only [C, Set.mem_iUnion]
  exact ⟨g, ⟨⟨y, hg, hyL⟩, hgP⟩, hg⟩

/-- The union of the translates of a compact set over an index set is closed. -/
theorem isClosed_biUnion_smul_compact (A : Set Space) (hA : IsCompact A) (P : Set principalSix) :
    IsClosed (⋃ g ∈ P, g • A) := by
  refine isClosed_biUnion_smul A hA.isClosed (fun L hL => ?_) P
  refine (transporter_finite_six A L hA hL).subset ?_
  rintro g ⟨y, hy, hyL⟩
  obtain ⟨S, hS, rfl⟩ := Set.mem_smul_set.mp hy
  exact ⟨S, hS, hyL⟩

/-- The union of all translates of a compact set is closed. -/
theorem isClosed_saturation (A : Set Space) (hA : IsCompact A) :
    IsClosed (⋃ g : principalSix, g • A) := by
  have := isClosed_biUnion_smul_compact A hA Set.univ
  simpa using this

/-- Every compact set lies in a coordinate cube. -/
theorem exists_cube_bound (K : Set Space) (hK : IsCompact K) : ∃ n : ℕ, K ⊆ boxC n n := by
  obtain ⟨C, hC⟩ := (hK.image coordHomeo.continuous).isBounded.exists_norm_le
  refine ⟨⌈C⌉₊, fun S hS => ?_⟩
  have h := hC _ ⟨S, hS, rfl⟩
  have h1 : ‖(coordHomeo S).1‖ ≤ ⌈C⌉₊ :=
    (norm_fst_le _).trans (h.trans (Nat.le_ceil C))
  have h2 : ‖(coordHomeo S).2‖ ≤ ⌈C⌉₊ :=
    (norm_snd_le _).trans (h.trans (Nat.le_ceil C))
  exact ⟨by simpa [dist_zero_right] using h1, by simpa [dist_zero_right] using h2⟩

/-- A compact set has bounded log-pivot coordinates. -/
theorem exists_t_bound (A : Set Space) (hA : IsCompact A) : ∃ T : ℝ, ∀ S ∈ A, ‖(coordHomeo S).2‖ < T := by
  obtain ⟨n, hn⟩ := exists_cube_bound A hA
  refine ⟨n + 1, fun S hS => ?_⟩
  have := (hn hS).2
  have h2 : ‖(coordHomeo S).2‖ ≤ n := by simpa [dist_zero_right] using this
  linarith

/-- **A thin tube with finitely many sheets over every compact.**  Given a closed set `N` missing the
flat there is a continuous positive radius `ρ' ≤ ε`, below `‖π‖` on `N`, such that the closed tube
`{‖π‖ ≤ ρ'}` meets the level six translates of any compact set in finitely many sheets. -/
theorem tube_proper (ε : ℝ) (hε : 0 < ε) (N : Set Space) (hN : IsClosed N) (hNF : ∀ S ∈ N, S ∉ flat) :
    ∃ ρ' : Space → ℝ, Continuous ρ' ∧ (∀ S, 0 < ρ' S) ∧ (∀ S, ρ' S ≤ ε) ∧
      (∀ S ∈ N, ρ' S < ‖piR3 S‖) ∧
      ∀ K : Set Space, IsCompact K →
        {g : principalSix | ((g • K) ∩ {S | ‖piR3 S‖ ≤ ρ' S}).Nonempty}.Finite := by
  have : TopologicalSpace.MetrizableSpace Space := coordHomeo.isEmbedding.metrizableSpace
  -- the cubes
  have hCc : ∀ n : ℕ, IsCompact (boxC (n : ℝ) (n : ℝ)) := fun n => isCompact_boxC _ _
  -- the flat points met by translates of the n-th cube are in a compact set
  have hbound : ∀ n : ℕ, ∃ T : ℝ, (n : ℝ) ≤ T ∧ ∀ g : principalSix, ∀ S ∈ boxC (n : ℝ) (n : ℝ),
      g • S ∈ flat → ‖(coordHomeo (g • S)).2‖ < T := by
    intro n
    have hfin : {g : principalSix | ∃ S ∈ boxC (n : ℝ) (n : ℝ), g • S ∈ flat}.Finite := by
      have h := finite_flat_transporter _ (hCc n)
      refine (h.preimage (Subtype.val_injective.injOn)).subset ?_
      rintro g ⟨S, hS, hgS⟩
      exact ⟨S, hS, hgS⟩
    let U : Set Space := ⋃ g ∈ {g : principalSix | ∃ S ∈ boxC (n : ℝ) (n : ℝ), g • S ∈ flat},
      g • boxC (n : ℝ) (n : ℝ)
    have hU : IsCompact U :=
      hfin.isCompact_biUnion fun g _ => (hCc n).image (continuous_smul_six g)
    obtain ⟨T0, hT0⟩ := exists_t_bound U hU
    refine ⟨max T0 n, le_max_right _ _, fun g S hS hgS => ?_⟩
    have : g • S ∈ U := by
      simp only [U, Set.mem_iUnion]
      exact ⟨g, ⟨S, hS, hgS⟩, Set.smul_mem_smul_set hS⟩
    exact lt_of_lt_of_le (hT0 _ this) (le_max_left _ _)
  choose T hTn hT using hbound
  -- the closed set to avoid
  let Nn : ℕ → Set Space := fun n =>
    (⋃ g : principalSix, g • boxC (n : ℝ) (n : ℝ)) ∩ {S | T n ≤ ‖(coordHomeo S).2‖}
  have hNnc : ∀ n, IsClosed (Nn n) := fun n =>
    (isClosed_saturation _ (hCc n)).inter
      (isClosed_le continuous_const (continuous_norm.comp (continuous_snd.comp coordHomeo.continuous)))
  have hNnF : ∀ n, ∀ S ∈ Nn n, S ∉ flat := by
    rintro n S ⟨hS1, hS2⟩ hSf
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hS1
    obtain ⟨c, hc, rfl⟩ := Set.mem_smul_set.mp hg
    exact absurd (hT n g c hc hSf) (not_lt.mpr hS2)
  have hloc : LocallyFinite Nn := by
    intro x
    obtain ⟨m, hm⟩ := exists_nat_gt ‖(coordHomeo x).2‖
    refine ⟨coordHomeo ⁻¹' (Set.univ ×ˢ Metric.ball (0 : R2) m), ?_, ?_⟩
    · refine (IsOpen.mem_nhds ?_ ?_)
      · exact (isOpen_univ.prod Metric.isOpen_ball).preimage coordHomeo.continuous
      · exact ⟨Set.mem_univ _, by simpa [dist_zero_right] using hm⟩
    · refine (Set.finite_lt_nat m).subset ?_
      rintro n ⟨S, ⟨_, hS2⟩, _, hS3⟩
      have h3 : ‖(coordHomeo S).2‖ < m := by simpa [dist_zero_right] using hS3
      have : (n : ℝ) < m := lt_of_le_of_lt (hTn n) (lt_of_le_of_lt hS2 h3)
      exact_mod_cast this
  have hNall : IsClosed (N ∪ ⋃ n, Nn n) := hN.union (hloc.isClosed_iUnion hNnc)
  have hNallF : ∀ S ∈ N ∪ ⋃ n, Nn n, 0 < ‖piR3 S‖ := by
    intro S hS
    rcases hS with hS | hS
    · exact norm_pos_iff.mpr fun h => hNF S hS h
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hS
      exact norm_pos_iff.mpr fun h => hNnF n S hn h
  obtain ⟨ρ', hρc, hρpos, hρε, hρN⟩ := exists_tube_radius (fun S : Space => ‖piR3 S‖)
    (continuous_norm.comp piR3.continuous) _ hNall hNallF ε hε
  refine ⟨ρ', hρc, hρpos, hρε, fun S hS => hρN S (Or.inl hS), ?_⟩
  intro K hK
  obtain ⟨n, hn⟩ := exists_cube_bound K hK
  refine (transporter_finite_six _ _ hK (isCompact_boxC ε (T n))).subset ?_
  rintro g ⟨x, ⟨S, hSK, rfl⟩, hxZ⟩
  refine ⟨S, hSK, ?_⟩
  have hx_in : g • S ∈ ⋃ g : principalSix, g • boxC (n : ℝ) (n : ℝ) :=
    Set.mem_iUnion.mpr ⟨g, Set.smul_mem_smul_set (hn hSK)⟩
  have ht : ‖(coordHomeo (g • S)).2‖ < T n := by
    by_contra hcon
    have hNx : g • S ∈ Nn n := ⟨hx_in, not_lt.mp hcon⟩
    have := hρN _ (Or.inr (Set.mem_iUnion.mpr ⟨n, hNx⟩))
    exact absurd hxZ (not_le.mpr this)
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, coordHomeo_fst]
    exact hxZ.trans (hρε _)
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact ht.le

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
