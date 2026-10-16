module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Average
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.BoxNeighborhood

@[expose] public section


/-! # General coercivity, Tier B (phase F): equivariant cutoffs adapted to coordinate boxes

For an admissible group `Γ` there is a family of affine coordinate boxes `B_i ⊆ positiveCoordinates`
and smooth compactly supported bumps `χ_i` with `tsupport χ_i ⊆ B_i` such that the `Γ`-translates of
the `χ_i` form a locally finite family on the positive coordinates and `∑_{γ,i} χ_i ∘ γ > 0`
everywhere.  Normalising by the invariant sum gives an equivariant partition of unity.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialFormWeakSmooth
open Set Filter Topology TernaryPoly.CompactCoordinateIntegration
open scoped ContDiff

variable {Γ : Subgroup RealGL}

/-! ### Saturation -/

/-- The `Γ`-saturation of a set of coordinates. -/
def satur (Γ : Subgroup RealGL) (S : Set Coordinates) : Set Coordinates :=
  ⋃ γ : Γ, coordinateAction (γ : RealGL) '' S

theorem mem_satur {S : Set Coordinates} {y : Coordinates} :
    y ∈ satur Γ S ↔ ∃ γ : Γ, ∃ x ∈ S, coordinateAction (γ : RealGL) x = y := by
  simp [satur]

theorem satur_mono {S T : Set Coordinates} (h : S ⊆ T) : satur Γ S ⊆ satur Γ T := by
  intro y hy
  obtain ⟨γ, x, hx, rfl⟩ := mem_satur.mp hy
  exact mem_satur.mpr ⟨γ, x, h hx, rfl⟩

theorem subset_satur {S : Set Coordinates} (hS : S ⊆ positiveCoordinates) : S ⊆ satur Γ S := by
  intro x hx
  exact mem_satur.mpr ⟨1, x, hx, coordinateAction_one (hS hx)⟩

theorem satur_subset_positive {S : Set Coordinates} (hS : S ⊆ positiveCoordinates) :
    satur Γ S ⊆ positiveCoordinates := by
  intro y hy
  obtain ⟨γ, x, hx, rfl⟩ := mem_satur.mp hy
  exact coordinateAction_mem (γ : RealGL) x (hS hx)

theorem isOpen_satur {S : Set Coordinates} (hS : S ⊆ positiveCoordinates) (ho : IsOpen S) :
    IsOpen (satur Γ S) := by
  unfold satur
  refine isOpen_iUnion fun γ => ?_
  exact (actionCoordinates (γ : RealGL)).isOpen_image_of_subset_source ho hS

theorem coordinateAction_inv_action (γ : Γ) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coordinateAction ((γ⁻¹ : Γ) : RealGL) (coordinateAction (γ : RealGL) x) = x := by
  rw [Subgroup.coe_inv]
  exact coordinateAction_inv_apply (γ : RealGL) hx

theorem isOpen_diff_satur (h : Admissible Γ) {K : Set Coordinates} (hK : IsCompact K)
    (hKp : K ⊆ positiveCoordinates) : IsOpen (positiveCoordinates \ satur Γ K) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hx, hxs⟩
  obtain ⟨N, hNn, hNp, hfin⟩ := h.translates_locallyFinite hK hKp x hx
  classical
  let F := hfin.toFinset
  let C : Set Coordinates := ⋃ g ∈ F, coordinateAction ((g⁻¹ : Γ) : RealGL) '' K
  have hCc : IsCompact C := F.isCompact_biUnion fun g _ =>
    hK.image_of_continuousOn ((contDiffOn_coordinateAction ((g⁻¹ : Γ) : RealGL)).continuousOn.mono hKp)
  have hxC : x ∉ C := by
    intro hxc
    obtain ⟨g, -, hg⟩ := mem_iUnion₂.mp hxc
    exact hxs (mem_satur.mpr ⟨g⁻¹, hg⟩)
  have hnhd : N ∩ Cᶜ ∈ 𝓝 x := inter_mem hNn (hCc.isClosed.isOpen_compl.mem_nhds hxC)
  filter_upwards [hnhd] with y ⟨hyN, hyC⟩
  refine ⟨hNp hyN, fun hys => hyC ?_⟩
  obtain ⟨γ, k, hk, rfl⟩ := mem_satur.mp hys
  refine mem_iUnion₂.mpr ⟨γ⁻¹, ?_, ⟨k, hk, ?_⟩⟩
  · rw [Set.Finite.mem_toFinset]
    exact ⟨_, hyN, by rw [coordinateAction_inv_action γ (hKp hk)]; exact hk⟩
  · rw [inv_inv]

/-! ### Exhaustion of the positive coordinates -/

theorem exists_exhaustion :
    ∃ K U : ℕ → Set Coordinates, (∀ m, IsCompact (K m)) ∧ (∀ m, K m ⊆ positiveCoordinates) ∧
      (∀ m, IsOpen (U m)) ∧ (∀ m, U m ⊆ K m) ∧ (∀ m, K m ⊆ U (m + 1)) ∧
      (∀ x ∈ positiveCoordinates, ∃ m, x ∈ U m) := by
  have : LocallyCompactSpace ↥positiveCoordinates :=
    isOpen_positiveCoordinates.locallyCompactSpace
  let KE := CompactExhaustion.choice ↥positiveCoordinates
  refine ⟨fun m => Subtype.val '' (KE m), fun m => Subtype.val '' interior (KE m), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact fun m => (KE.isCompact m).image continuous_subtype_val
  · exact fun m => Subtype.coe_image_subset _ _
  · exact fun m => isOpen_positiveCoordinates.isOpenMap_subtype_val _ isOpen_interior
  · exact fun m => image_mono interior_subset
  · exact fun m => image_mono (KE.subset_interior_succ m)
  · intro x hx
    have : (⟨x, hx⟩ : ↥positiveCoordinates) ∈ ⋃ m, KE m := by rw [KE.iUnion_eq]; trivial
    obtain ⟨m, hm⟩ := mem_iUnion.mp this
    exact ⟨m + 1, ⟨⟨x, hx⟩, KE.subset_interior_succ m hm, rfl⟩⟩

/-! ### Compact sets and translates -/

theorem Admissible.translates_finite_compact (h : Admissible Γ) {A D : Set Coordinates}
    (hA : IsCompact A) (hAp : A ⊆ positiveCoordinates) (hD : IsCompact D)
    (hDp : D ⊆ positiveCoordinates) :
    {γ : Γ | ∃ y ∈ A, coordinateAction (γ : RealGL) y ∈ D}.Finite := by
  have hloc : ∀ y ∈ A, ∃ N ∈ 𝓝 y, N ⊆ positiveCoordinates ∧
      {γ : Γ | ∃ z ∈ N, coordinateAction (γ : RealGL) z ∈ D}.Finite := fun y hy => by
    obtain ⟨N, hN, hNp, hf⟩ := h.translates_locallyFinite hD hDp y (hAp hy)
    exact ⟨N, hN, hNp, hf⟩
  choose! N hNn hNp hNf using hloc
  obtain ⟨t, htA, hcov⟩ := hA.elim_nhds_subcover N hNn
  refine (t.finite_toSet.biUnion fun y hy => hNf y (htA y hy)).subset ?_
  rintro γ ⟨y, hyA, hyD⟩
  obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.mp (hcov hyA)
  exact mem_iUnion₂.mpr ⟨z, hzt, ⟨y, hyz, hyD⟩⟩

/-! ### Boxes and bumps -/

theorem exists_box_bump {O : Set Coordinates} (hO : IsOpen O) {x : Coordinates} (hx : x ∈ O) :
    ∃ (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates) (χ : Coordinates → ℝ),
      x ∈ coordinateTestBox e a ∧ (coordinateTestBox e a : Set Coordinates) ⊆ O ∧
      IsCompact (closure (coordinateTestBox e a : Set Coordinates)) ∧ ContDiff ℝ ∞ χ ∧
      (∀ y, 0 ≤ χ y) ∧ HasCompactSupport χ ∧ tsupport χ ⊆ (coordinateTestBox e a : Set Coordinates) ∧
      0 < χ x := by
  obtain ⟨e, a, hxe, heO, hec⟩ := exists_coordinateTestBox_in_open hO hx
  obtain ⟨χ, hχs, hχc, hχd, hχr, hχx⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    ((coordinateTestBox e a).isOpen.mem_nhds hxe)
  exact ⟨e, a, χ, hxe, heO, hec, hχd, fun y => (hχr ⟨y, rfl⟩).1, hχc, hχs, by rw [hχx]; exact one_pos⟩

/-! ### The family of boxes and bumps -/

/-- Shift of a sequence of sets: empty below `k`. -/
def shiftSet (A : ℕ → Set Coordinates) (k m : ℕ) : Set Coordinates :=
  if k ≤ m then A (m - k) else ∅

theorem shiftSet_of_le {A : ℕ → Set Coordinates} {k m : ℕ} (h : k ≤ m) :
    shiftSet A k m = A (m - k) := ite_eq_left h

theorem shiftSet_of_lt {A : ℕ → Set Coordinates} {k m : ℕ} (h : m < k) :
    shiftSet A k m = ∅ := ite_eq_right (not_le.mpr h)

theorem Admissible.exists_box_cutoffs (h : Admissible Γ) :
    ∃ (ι : Type) (e : ι → WeakCubeFive ≃L[ℝ] Coordinates) (a : ι → Coordinates)
      (χ : ι → Coordinates → ℝ),
      (∀ i, (coordinateTestBox (e i) (a i) : Set Coordinates) ⊆ positiveCoordinates) ∧
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ i y, 0 ≤ χ i y) ∧ (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ (coordinateTestBox (e i) (a i) : Set Coordinates)) ∧
      (∀ x ∈ positiveCoordinates, ∃ N ∈ 𝓝 x,
        {p : Γ × ι | ∃ y ∈ N, coordinateAction (p.1 : RealGL) y ∈ tsupport (χ p.2)}.Finite) ∧
      (∀ x ∈ positiveCoordinates, ∃ (γ : Γ) (i : ι), 0 < χ i (coordinateAction (γ : RealGL) x)) := by
  classical
  obtain ⟨K, U, hKc, hKp, hUo, hUK, hKU, hcov⟩ := exists_exhaustion
  have hKmono : Monotone K := monotone_nat_of_le_succ fun m => (hKU m).trans (hUK _)
  have hUp : ∀ m, U m ⊆ positiveCoordinates := fun m => (hUK m).trans (hKp m)
  let Ub := shiftSet U 1
  let Kb := shiftSet K 2
  have hUbp : ∀ m, Ub m ⊆ positiveCoordinates := fun m => by
    by_cases hm : 1 ≤ m
    · rw [show Ub m = U (m - 1) from shiftSet_of_le hm]; exact hUp _
    · rw [show Ub m = ∅ from shiftSet_of_lt (not_le.mp hm)]; exact empty_subset _
  have hUbo : ∀ m, IsOpen (Ub m) := fun m => by
    by_cases hm : 1 ≤ m
    · rw [show Ub m = U (m - 1) from shiftSet_of_le hm]; exact hUo _
    · rw [show Ub m = ∅ from shiftSet_of_lt (not_le.mp hm)]; exact isOpen_empty
  have hKbc : ∀ m, IsCompact (Kb m) := fun m => by
    by_cases hm : 2 ≤ m
    · rw [show Kb m = K (m - 2) from shiftSet_of_le hm]; exact hKc _
    · rw [show Kb m = ∅ from shiftSet_of_lt (not_le.mp hm)]; exact isCompact_empty
  have hKbp : ∀ m, Kb m ⊆ positiveCoordinates := fun m => by
    by_cases hm : 2 ≤ m
    · rw [show Kb m = K (m - 2) from shiftSet_of_le hm]; exact hKp _
    · rw [show Kb m = ∅ from shiftSet_of_lt (not_le.mp hm)]; exact empty_subset _
  have hKbU : ∀ m, Kb m ⊆ Ub m := fun m => by
    by_cases hm : 2 ≤ m
    · rw [show Kb m = K (m - 2) from shiftSet_of_le hm,
        show Ub m = U (m - 1) from shiftSet_of_le (by omega)]
      have := hKU (m - 2)
      rwa [show m - 2 + 1 = m - 1 by omega] at this
    · rw [show Kb m = ∅ from shiftSet_of_lt (not_le.mp hm)]; exact empty_subset _
  let C : ℕ → Set Coordinates := fun m => K m \ satur Γ (Ub m)
  have hCc : ∀ m, IsCompact (C m) := fun m => (hKc m).diff (isOpen_satur (hUbp m) (hUbo m))
  have hCR : ∀ m, C m ⊆ positiveCoordinates \ satur Γ (Kb m) := fun m x hx =>
    ⟨hKp m hx.1, fun hs => hx.2 (satur_mono (hKbU m) hs)⟩
  have key : ∀ m, ∀ x ∈ C m, ∃ (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates)
      (χ : Coordinates → ℝ), x ∈ coordinateTestBox e a ∧
      (coordinateTestBox e a : Set Coordinates) ⊆ positiveCoordinates \ satur Γ (Kb m) ∧
      IsCompact (closure (coordinateTestBox e a : Set Coordinates)) ∧ ContDiff ℝ ∞ χ ∧
      (∀ y, 0 ≤ χ y) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ (coordinateTestBox e a : Set Coordinates) ∧ 0 < χ x := fun m x hx =>
    exists_box_bump (isOpen_diff_satur h (hKbc m) (hKbp m)) (hCR m hx)
  choose e a χ hxbox hboxO hcl hχd hχ0 hχc hχt hχx using key
  have hfin : ∀ m, ∃ t : Finset ↥(C m), C m ⊆ ⋃ x ∈ t, {y | 0 < χ m x.1 x.2 y} := fun m =>
    (hCc m).elim_nhds_subcover' (fun x hx => {y | 0 < χ m x hx y})
      (fun x hx => (isOpen_lt continuous_const (hχd m x hx).continuous).mem_nhds (hχx m x hx))
  choose t ht using hfin
  have hboxP : ∀ m x (hx : x ∈ C m), (coordinateTestBox (e m x hx) (a m x hx) : Set Coordinates) ⊆
      positiveCoordinates := fun m x hx => (hboxO m x hx).trans sdiff_subset
  refine ⟨Σ m : ℕ, {x : ↥(C m) // x ∈ t m},
    fun i => e i.1 i.2.1.1 i.2.1.2, fun i => a i.1 i.2.1.1 i.2.1.2,
    fun i => χ i.1 i.2.1.1 i.2.1.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hboxP _ _ _
  · exact fun i => hχd _ _ _
  · exact fun i => hχ0 _ _ _
  · exact fun i => hχc _ _ _
  · exact fun i => hχt _ _ _
  · intro x hx
    obtain ⟨M, hM⟩ := hcov x hx
    refine ⟨U M, (hUo M).mem_nhds hM, ?_⟩
    have hI0 : {i : Σ m : ℕ, {x : ↥(C m) // x ∈ t m} | i.1 < M + 2}.Finite := by
      refine ((Finset.range (M + 2)).finite_toSet.biUnion fun m _ =>
        (Set.finite_range (Sigma.mk (β := fun m : ℕ => {x : ↥(C m) // x ∈ t m}) m))).subset ?_
      intro i hi
      exact mem_iUnion₂.mpr ⟨i.1, by simpa using hi, ⟨i.2, rfl⟩⟩
    have hG : ∀ i : Σ m : ℕ, {x : ↥(C m) // x ∈ t m},
        {γ : Γ | ∃ y ∈ K M, coordinateAction (γ : RealGL) y ∈
          tsupport (χ i.1 i.2.1.1 i.2.1.2)}.Finite := fun i =>
      h.translates_finite_compact (hKc M) (hKp M) (hχc _ _ _).isCompact
        ((hχt _ _ _).trans (hboxP _ _ _))
    refine (hI0.biUnion fun i _ => (hG i).image (fun γ => (γ, i))).subset ?_
    rintro ⟨γ, i⟩ ⟨y, hyU, hyt⟩
    have hyK : y ∈ K M := hUK M hyU
    have hlt : i.1 < M + 2 := by
      by_contra hge
      have hge' : M + 2 ≤ i.1 := not_lt.mp hge
      have hyKb : y ∈ Kb i.1 := by
        rw [show Kb i.1 = K (i.1 - 2) from shiftSet_of_le (by omega)]
        exact hKmono (by omega) hyK
      have := (hboxO i.1 i.2.1.1 i.2.1.2) (hχt _ _ _ hyt)
      exact this.2 (mem_satur.mpr ⟨γ, y, hyKb, rfl⟩)
    exact mem_iUnion₂.mpr ⟨i, hlt, ⟨γ, ⟨y, hyK, hyt⟩, rfl⟩⟩
  · intro x hx
    have hP : ∃ m, ∃ γ : Γ, coordinateAction (γ : RealGL) x ∈ U m := by
      obtain ⟨m, hm⟩ := hcov x hx
      exact ⟨m, 1, by rwa [show ((1 : Γ) : RealGL) = 1 from rfl, coordinateAction_one hx]⟩
    let m0 := Nat.find hP
    obtain ⟨γ0, hγ0⟩ := Nat.find_spec hP
    have hyC : coordinateAction (γ0 : RealGL) x ∈ C m0 := by
      refine ⟨hUK m0 hγ0, fun hys => ?_⟩
      by_cases hm0 : 1 ≤ m0
      · rw [show Ub m0 = U (m0 - 1) from shiftSet_of_le hm0] at hys
        obtain ⟨δ, u, hu, hδu⟩ := mem_satur.mp hys
        have hupos : u ∈ positiveCoordinates := hUp _ hu
        have hux : u = coordinateAction ((δ⁻¹ * γ0 : Γ) : RealGL) x := by
          rw [Subgroup.coe_mul, coordinateAction_mul _ _ hx, ← hδu,
            coordinateAction_inv_action δ hupos]
        exact Nat.find_min hP (show m0 - 1 < m0 by omega)
          ⟨δ⁻¹ * γ0, by rw [← hux]; exact hu⟩
      · rw [show Ub m0 = ∅ from shiftSet_of_lt (not_le.mp hm0)] at hys
        obtain ⟨_, _, hxe, _⟩ := mem_satur.mp hys
        exact hxe
    obtain ⟨x', hx't, hx'y⟩ := mem_iUnion₂.mp (ht m0 hyC)
    exact ⟨γ0, ⟨m0, ⟨x', hx't⟩⟩, hx'y⟩

/-! ### Locally finite sums of translates -/

section Sums

variable {ι : Type} (χ : ι → Coordinates → ℝ)

/-- The index set of translates meeting a neighbourhood. -/
def meetSet (Γ : Subgroup RealGL) (N : Set Coordinates) : Set (Γ × ι) :=
  {p | ∃ y ∈ N, coordinateAction (p.1 : RealGL) y ∈ tsupport (χ p.2)}

theorem finsum_translates_eq_sum {N : Set Coordinates} (hS : (meetSet (Γ := Γ) χ N).Finite)
    {y : Coordinates} (hy : y ∈ N) :
    ∑ᶠ p : Γ × ι, χ p.2 (coordinateAction (p.1 : RealGL) y) =
      ∑ p ∈ hS.toFinset, χ p.2 (coordinateAction (p.1 : RealGL) y) := by
  apply finsum_eq_sum_of_support_subset
  intro p hp
  rw [Function.mem_support] at hp
  rw [Finset.mem_coe, Set.Finite.mem_toFinset]
  exact ⟨y, hy, subset_tsupport _ hp⟩

theorem contDiffOn_finsum_translates (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hlf : ∀ x ∈ positiveCoordinates, ∃ N ∈ 𝓝 x, (meetSet (Γ := Γ) χ N).Finite) :
    ContDiffOn ℝ ∞ (fun y => ∑ᶠ p : Γ × ι, χ p.2 (coordinateAction (p.1 : RealGL) y))
      positiveCoordinates := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨N, hN, hS⟩ := hlf x hx
  refine ⟨interior N, isOpen_interior, mem_interior_iff_mem_nhds.mpr hN, ?_⟩
  have hsum : ContDiffOn ℝ ∞ (fun y => ∑ p ∈ hS.toFinset, χ p.2 (coordinateAction (p.1 : RealGL) y))
      (positiveCoordinates ∩ interior N) :=
    ContDiffOn.sum fun p _ => ((hχ p.2).comp_contDiffOn
      (contDiffOn_coordinateAction (p.1 : RealGL))).mono inter_subset_left
  exact hsum.congr fun y hy => finsum_translates_eq_sum χ hS (interior_subset hy.2)

theorem finsum_translates_invariant (δ : Γ) {y : Coordinates} (hy : y ∈ positiveCoordinates) :
    ∑ᶠ p : Γ × ι, χ p.2 (coordinateAction (p.1 : RealGL) (coordinateAction (δ : RealGL) y)) =
      ∑ᶠ p : Γ × ι, χ p.2 (coordinateAction (p.1 : RealGL) y) := by
  have e1 : ∀ p : Γ × ι, χ p.2 (coordinateAction (p.1 : RealGL) (coordinateAction (δ : RealGL) y)) =
      (fun q : Γ × ι => χ q.2 (coordinateAction (q.1 : RealGL) y))
        (Equiv.prodCongr (Equiv.mulRight δ) (Equiv.refl ι) p) := fun p => by
    show χ p.2 (coordinateAction (p.1 : RealGL) (coordinateAction (δ : RealGL) y)) =
      χ p.2 (coordinateAction ((p.1 * δ : Γ) : RealGL) y)
    rw [Subgroup.coe_mul, coordinateAction_mul _ _ hy]
  simp only [e1]
  exact finsum_comp_equiv (Equiv.prodCongr (Equiv.mulRight δ) (Equiv.refl ι))
    (f := fun q : Γ × ι => χ q.2 (coordinateAction (q.1 : RealGL) y))

end Sums

/-! ### The equivariant partition of unity subordinate to the boxes -/

/-- A family of coordinate boxes with an equivariant smooth partition of unity subordinate to it:
the bumps `ρ_i` have compact support inside the box `B_i ⊆ positiveCoordinates`, the translates
`ρ_i ∘ γ` are locally finite, and `∑_{γ,i} ρ_i ∘ γ = 1` on the positive coordinates. -/
structure BoxData (Γ : Subgroup RealGL) where
  ι : Type
  e : ι → WeakCubeFive ≃L[ℝ] Coordinates
  a : ι → Coordinates
  ρ : ι → Coordinates → ℝ
  box_pos : ∀ i, (coordinateTestBox (e i) (a i) : Set Coordinates) ⊆ positiveCoordinates
  smooth : ∀ i, ContDiff ℝ ∞ (ρ i)
  nonneg : ∀ i y, 0 ≤ ρ i y
  compact : ∀ i, HasCompactSupport (ρ i)
  tsupport_subset : ∀ i, tsupport (ρ i) ⊆ (coordinateTestBox (e i) (a i) : Set Coordinates)
  locFin : ∀ x ∈ positiveCoordinates, ∃ N ∈ 𝓝 x, (meetSet (Γ := Γ) ρ N).Finite
  sum_one : ∀ x ∈ positiveCoordinates,
    ∑ᶠ p : Γ × ι, ρ p.2 (coordinateAction (p.1 : RealGL) x) = 1

theorem Admissible.nonempty_boxData (h : Admissible Γ) : Nonempty (BoxData Γ) := by
  classical
  obtain ⟨ι, e, a, χ, hbox, hχd, hχ0, hχc, hχt, hlf, hcov⟩ := h.exists_box_cutoffs
  let Z : Coordinates → ℝ := fun y => ∑ᶠ p : Γ × ι, χ p.2 (coordinateAction (p.1 : RealGL) y)
  have hlf' : ∀ x ∈ positiveCoordinates, ∃ N ∈ 𝓝 x, (meetSet (Γ := Γ) χ N).Finite := hlf
  have hZs : ContDiffOn ℝ ∞ Z positiveCoordinates := contDiffOn_finsum_translates χ hχd hlf'
  have hZpos : ∀ x ∈ positiveCoordinates, 0 < Z x := by
    intro x hx
    obtain ⟨γ, i, hγi⟩ := hcov x hx
    obtain ⟨N, hN, hS⟩ := hlf' x hx
    have hp : (γ, i) ∈ hS.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨x, mem_of_mem_nhds hN, subset_tsupport _ (ne_of_gt hγi)⟩
    show 0 < ∑ᶠ p : Γ × ι, χ p.2 (coordinateAction (p.1 : RealGL) x)
    rw [finsum_translates_eq_sum χ hS (mem_of_mem_nhds hN)]
    exact lt_of_lt_of_le hγi (Finset.single_le_sum (f := fun p : Γ × ι =>
      χ p.2 (coordinateAction (p.1 : RealGL) x)) (fun p _ => hχ0 _ _) hp)
  have hZinv : ∀ (δ : Γ), ∀ y ∈ positiveCoordinates, Z (coordinateAction (δ : RealGL) y) = Z y :=
    fun δ y hy => finsum_translates_invariant χ δ hy
  let ρ : ι → Coordinates → ℝ := fun i y => χ i y / Z y
  have hρs : ∀ i, ContDiff ℝ ∞ (ρ i) := by
    intro i
    have hon : ContDiffOn ℝ ∞ (ρ i) positiveCoordinates :=
      (hχd i).contDiffOn.div hZs (fun y hy => (hZpos y hy).ne')
    refine contDiff_of_tsupport_subset isOpen_positiveCoordinates hon ?_
    have : tsupport (ρ i) ⊆ tsupport (χ i) := by
      apply closure_mono
      intro y hy
      rw [Function.mem_support] at hy ⊢
      intro h0
      apply hy
      simp [ρ, h0]
    exact this.trans ((hχt i).trans (hbox i))
  have hρt : ∀ i, tsupport (ρ i) ⊆ tsupport (χ i) := by
    intro i
    apply closure_mono
    intro y hy
    rw [Function.mem_support] at hy ⊢
    intro h0
    apply hy
    simp [ρ, h0]
  refine ⟨⟨ι, e, a, ρ, hbox, hρs, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i y
    exact div_nonneg (hχ0 i y) (by
      by_cases hy : y ∈ positiveCoordinates
      · exact (hZpos y hy).le
      · exact finsum_nonneg fun p => hχ0 _ _)
  · exact fun i => IsCompact.of_isClosed_subset (hχc i) (isClosed_tsupport _) (hρt i)
  · exact fun i => (hρt i).trans (hχt i)
  · intro x hx
    obtain ⟨N, hN, hS⟩ := hlf' x hx
    refine ⟨N, hN, hS.subset ?_⟩
    rintro p ⟨y, hy, hyt⟩
    exact ⟨y, hy, hρt _ hyt⟩
  · intro x hx
    obtain ⟨N, hN, hS⟩ := hlf' x hx
    have hxN := mem_of_mem_nhds hN
    have hZx : Z x = ∑ p ∈ hS.toFinset, χ p.2 (coordinateAction (p.1 : RealGL) x) :=
      finsum_translates_eq_sum χ hS hxN
    have hterm : ∀ p : Γ × ι, ρ p.2 (coordinateAction (p.1 : RealGL) x) =
        χ p.2 (coordinateAction (p.1 : RealGL) x) / Z x := fun p => by
      change χ p.2 (coordinateAction (p.1 : RealGL) x) / Z (coordinateAction (p.1 : RealGL) x) = _
      rw [hZinv p.1 x hx]
    rw [finsum_eq_sum_of_support_subset (s := hS.toFinset) _ ?_]
    · simp_rw [hterm]
      rw [← Finset.sum_div, ← hZx]
      exact div_self (hZpos x hx).ne'
    · intro p hp
      rw [Function.mem_support, hterm] at hp
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      refine ⟨x, hxN, subset_tsupport _ ?_⟩
      intro h0
      exact hp (by rw [h0, zero_div])

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
