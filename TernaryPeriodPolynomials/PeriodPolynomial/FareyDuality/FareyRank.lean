module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyCusp

@[expose] public section


/-!
# Rank function on the dual Farey tree

Formalized by Claude Sonnet 5.5.

Two triangles of the Farey complex are adjacent in the dual tree (`TAdj`) if they are distinct and share an edge.
The rank `triRank` of a triangle is the largest `ℓ¹` norm of its cusps.  Main results:

* `rank_P1`: for every triangle `t`, at most one neighbour of `t` has rank at most `rank t`
  (the neighbours across edges through a maximal cusp have strictly larger rank, `rank_lt_of_max`);
* `rank_P2`: every triangle which is not one of the two *central* triangles `triPlus = {⟨e₁⟩,⟨e₂⟩,⟨e₁+e₂⟩}`,
  `triMinus = {⟨e₁⟩,⟨e₂⟩,⟨e₁-e₂⟩}` over the standard edge has a neighbour of strictly smaller rank
  (`central_iff` identifies the central triangles; the proof uses the Euclidean step `quadrant_dominates`);
* `tAdj_triPlus_triMinus`.

These two properties say that the dual Farey tree is a tree with a unique central edge `{⟨e₁⟩,⟨e₂⟩}`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FareyTree

open TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.RankTwoVertexLinks
  TernaryPoly.RankTwoHeightLinks

/-- Two distinct triangles sharing an edge are adjacent in the dual tree. -/
def TAdj (t t' : Tri) : Prop :=
  t ≠ t' ∧ ∃ x y, x ≠ y ∧ x ∈ t.1 ∧ y ∈ t.1 ∧ x ∈ t'.1 ∧ y ∈ t'.1

theorem TAdj.symm {t t' : Tri} (h : TAdj t t') : TAdj t' t := by
  obtain ⟨hne, x, y, hxy, hx, hy, hx', hy'⟩ := h
  exact ⟨hne.symm, x, y, hxy, hx', hy', hx, hy⟩

theorem tri_third {t : Tri} {x y : RationalLine2} (hx : x ∈ t.1) (hy : y ∈ t.1) (hxy : x ≠ y) :
    ∃ z, z ∈ t.1 ∧ z ≠ x ∧ z ≠ y ∧ t.1 = {x, y, z} := by
  obtain ⟨g, hg⟩ := t.2
  rw [hg] at hx hy ⊢
  exact exists_third hx hy hxy

theorem tri_adj {t : Tri} {x y : RationalLine2} (hx : x ∈ t.1) (hy : y ∈ t.1) (hxy : x ≠ y) :
    Adj x y := by
  obtain ⟨g, hg⟩ := t.2
  rw [hg] at hx hy
  exact frame_adj hx hy hxy

theorem tri_third_cases {t : Tri} {x y z : RationalLine2} (hx : x ∈ t.1) (hy : y ∈ t.1)
    (hz : z ∈ t.1) (hzx : z ≠ x) (hzy : z ≠ y) {a b : IntegralVector} (ha : IsGen x a)
    (hb : IsGen y b) (h : Unimod a b) : z = plusLine h ∨ z = minusLine h := by
  obtain ⟨g, hg⟩ := t.2
  rw [hg] at hx hy hz
  exact third_cases hx hy hz hzx hzy ha hb h

theorem cuspN_plus {x y : RationalLine2} {a b : IntegralVector} (ha : IsGen x a) (hb : IsGen y b)
    (h : Unimod a b) (h0 : 0 ≤ a 0 * b 0) (h1 : 0 ≤ a 1 * b 1) :
    cuspN (plusLine h) = cuspN x + cuspN y := by
  rw [cuspN_eq (isGen_plusLine h), cuspN_eq ha, cuspN_eq hb]
  exact N1_add_of_quadrant (a 0) (a 1) (b 0) (b 1) h0 h1

theorem cuspN_minus_lt {x y : RationalLine2} {a b : IntegralVector} (ha : IsGen x a) (hb : IsGen y b)
    (h : Unimod a b) (h0 : 0 ≤ a 0 * b 0) (h1 : 0 ≤ a 1 * b 1)
    (hne : a 0 * b 0 ≠ 0 ∨ a 1 * b 1 ≠ 0) : cuspN (minusLine h) < cuspN x + cuspN y := by
  rw [cuspN_eq (isGen_minusLine h), cuspN_eq ha, cuspN_eq hb]
  exact N1_sub_lt (a 0) (a 1) (b 0) (b 1) h0 h1 hne

/-- Across an edge through a maximal cusp, the neighbouring triangle has strictly larger rank. -/
theorem rank_lt_of_max {t t' : Tri} {x y : RationalLine2} (hx : x ∈ t.1) (hy : y ∈ t.1)
    (hx' : x ∈ t'.1) (hy' : y ∈ t'.1) (hxy : x ≠ y) (htt : t ≠ t')
    (hmax : cuspNat x = triRank t) : triRank t < triRank t' := by
  obtain ⟨z, hz, hzx, hzy, hzt⟩ := tri_third hx hy hxy
  obtain ⟨z', hz', hz'x, hz'y, hzt'⟩ := tri_third hx' hy' hxy
  have hzz : z ≠ z' := by
    intro e
    apply htt
    apply Subtype.ext
    rw [hzt, hzt', e]
  obtain ⟨a, b, ha, hb, h0, h1⟩ := (tri_adj hx hy hxy).common_quadrant
  have hu : Unimod a b := (tri_adj hx hy hxy).det ha hb
  have hpl : cuspN (plusLine hu) = cuspN x + cuspN y := cuspN_plus ha hb hu h0 h1
  have hy1 : 1 ≤ cuspN y := cuspN_pos y
  have hzc := tri_third_cases hx hy hz hzx hzy ha hb hu
  have hz'c := tri_third_cases hx' hy' hz' hz'x hz'y ha hb hu
  have hzle : cuspN z ≤ cuspN x := by
    have : cuspNat z ≤ cuspNat x := hmax ▸ le_triRank hz
    have := (Int.ofNat_le).mpr this
    rwa [cuspNat_cast, cuspNat_cast] at this
  have hz'plus : z' = plusLine hu := by
    rcases hz'c with e | e
    · exact e
    · exfalso
      rcases hzc with e2 | e2
      · rw [e2] at hzle; omega
      · exact hzz (e2.trans e.symm)
  have : cuspNat (plusLine hu) ≤ triRank t' := hz'plus ▸ le_triRank hz'
  have h2 : (cuspNat (plusLine hu) : ℤ) = cuspN x + cuspN y := by rw [cuspNat_cast, hpl]
  have h3 : (cuspNat x : ℤ) = cuspN x := cuspNat_cast x
  have h4 : (cuspNat (plusLine hu) : ℤ) ≤ triRank t' := by exact_mod_cast this
  have h5 : (cuspNat x : ℤ) = triRank t := by exact_mod_cast hmax
  omega

theorem pigeon2 {α : Type*} {u v p q r : α} (huv : u ≠ v) (hp : p = u ∨ p = v) (hq : q = u ∨ q = v)
    (hr : r = u ∨ r = v) (hpq : p ≠ q) (hpr : p ≠ r) : q = r := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;> simp_all

theorem rank_gt_of_max_mem {t t' : Tri} {x y w : RationalLine2} (hx : x ∈ t.1) (hy : y ∈ t.1)
    (hx' : x ∈ t'.1) (hy' : y ∈ t'.1) (hxy : x ≠ y) (htt : t ≠ t')
    (hw : w = x ∨ w = y) (hmax : cuspNat w = triRank t) : triRank t < triRank t' := by
  rcases hw with rfl | rfl
  · exact rank_lt_of_max hx hy hx' hy' hxy htt hmax
  · exact rank_lt_of_max hy hx hy' hx' hxy.symm htt hmax

/-- At most one neighbour of a triangle has rank at most its own. -/
theorem rank_P1 {t t₁ t₂ : Tri} (h₁ : TAdj t t₁) (h₂ : TAdj t t₂) (hne : t₁ ≠ t₂) :
    ¬ (triRank t₁ ≤ triRank t ∧ triRank t₂ ≤ triRank t) := by
  rintro ⟨r1, r2⟩
  obtain ⟨w, hw, hwmax⟩ := exists_max_cusp t
  obtain ⟨hne1, x₁, y₁, hxy₁, hx₁, hy₁, hx₁', hy₁'⟩ := h₁
  obtain ⟨hne2, x₂, y₂, hxy₂, hx₂, hy₂, hx₂', hy₂'⟩ := h₂
  have w1 : w ≠ x₁ ∧ w ≠ y₁ := by
    constructor <;> intro e
    · have := rank_gt_of_max_mem hx₁ hy₁ hx₁' hy₁' hxy₁ hne1 (Or.inl e) hwmax
      omega
    · have := rank_gt_of_max_mem hx₁ hy₁ hx₁' hy₁' hxy₁ hne1 (Or.inr e) hwmax
      omega
  have w2 : w ≠ x₂ ∧ w ≠ y₂ := by
    constructor <;> intro e
    · have := rank_gt_of_max_mem hx₂ hy₂ hx₂' hy₂' hxy₂ hne2 (Or.inl e) hwmax
      omega
    · have := rank_gt_of_max_mem hx₂ hy₂ hx₂' hy₂' hxy₂ hne2 (Or.inr e) hwmax
      omega
  obtain ⟨z₁, hz₁, hz₁x, hz₁y, ht₁⟩ := tri_third hx₁ hy₁ hxy₁
  obtain ⟨z₂, hz₂, hz₂x, hz₂y, ht₂⟩ := tri_third hx₂ hy₂ hxy₂
  have hwz₁ : w = z₁ := by
    rw [ht₁] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with e | e | e
    · exact absurd e w1.1
    · exact absurd e w1.2
    · exact e
  have hwz₂ : w = z₂ := by
    rw [ht₂] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with e | e | e
    · exact absurd e w2.1
    · exact absurd e w2.2
    · exact e
  -- x₁, y₁ lie in `t₂`
  have hx₁t₂ : x₁ ∈ t₂.1 := by
    have : x₁ ∈ t.1 := hx₁
    rw [ht₂] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e | e | e
    · exact e ▸ hx₂'
    · exact e ▸ hy₂'
    · exact absurd (e.symm ▸ hwz₂.symm ▸ rfl : w = x₁) w1.1
  have hy₁t₂ : y₁ ∈ t₂.1 := by
    have : y₁ ∈ t.1 := hy₁
    rw [ht₂] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e | e | e
    · exact e ▸ hx₂'
    · exact e ▸ hy₂'
    · exact absurd (e.symm ▸ hwz₂.symm ▸ rfl : w = y₁) w1.2
  obtain ⟨z₂', hz₂', hz₂'x, hz₂'y, ht₂'⟩ := tri_third hx₁t₂ hy₁t₂ hxy₁
  obtain ⟨z₁', hz₁', hz₁'x, hz₁'y, ht₁'⟩ := tri_third hx₁' hy₁' hxy₁
  obtain ⟨a, b, ha, hb, -, -⟩ := (tri_adj hx₁ hy₁ hxy₁).common_quadrant
  have hu : Unimod a b := (tri_adj hx₁ hy₁ hxy₁).det ha hb
  have cw := tri_third_cases hx₁ hy₁ hw (hwz₁ ▸ hz₁x) (hwz₁ ▸ hz₁y) ha hb hu
  have c1 := tri_third_cases hx₁' hy₁' hz₁' hz₁'x hz₁'y ha hb hu
  have c2 := tri_third_cases hx₁t₂ hy₁t₂ hz₂' hz₂'x hz₂'y ha hb hu
  have hw1 : w ≠ z₁' := by
    intro e
    apply hne1
    apply Subtype.ext
    rw [ht₁, ht₁', ← hwz₁, e]
  have hw2 : w ≠ z₂' := by
    intro e
    apply hne2
    apply Subtype.ext
    rw [ht₁, ← hwz₁, ht₂', e]
  have hpm := plusLine_ne_minusLine hu
  have hz12 : z₁' = z₂' := pigeon2 hpm cw c1 c2 hw1 hw2
  apply hne
  apply Subtype.ext
  rw [ht₁', ht₂', hz12]

theorem cuspN_le_rank {t : Tri} {x : RationalLine2} (hx : x ∈ t.1) : cuspN x ≤ (triRank t : ℤ) := by
  have := le_triRank hx
  have h2 : (cuspNat x : ℤ) ≤ triRank t := by exact_mod_cast this
  rwa [cuspNat_cast] at h2

theorem cuspN_eq_rank {t : Tri} {w : RationalLine2} (h : cuspNat w = triRank t) :
    cuspN w = (triRank t : ℤ) := by
  rw [← cuspNat_cast, h]

/-- A triangle with two cusps of norm one (the two triangles over the standard edge). -/
def Central (t : Tri) : Prop :=
  ∃ x y, x ≠ y ∧ x ∈ t.1 ∧ y ∈ t.1 ∧ cuspN x = 1 ∧ cuspN y = 1

theorem tri_card (t : Tri) : t.1.card = 3 := by
  obtain ⟨g, hg⟩ := t.2
  rw [hg]; exact frame_card g

theorem tri_three (t : Tri) {w : RationalLine2} (hw : w ∈ t.1) :
    ∃ u v, u ∈ t.1 ∧ v ∈ t.1 ∧ u ≠ w ∧ v ≠ w ∧ u ≠ v ∧ t.1 = {w, u, v} := by
  obtain ⟨u, hu, huw⟩ := Finset.exists_mem_ne (s := t.1) (by rw [tri_card]; norm_num) w
  obtain ⟨v, hv, hvw, hvu, ht⟩ := tri_third hw hu huw.symm
  exact ⟨u, v, hu, hv, huw, hvw, hvu.symm, ht⟩

/-- Every non-central triangle has a neighbour of strictly smaller rank. -/
theorem rank_P2 {t : Tri} (hc : ¬ Central t) : ∃ t' : Tri, TAdj t t' ∧ triRank t' < triRank t := by
  obtain ⟨w, hw, hwmax⟩ := exists_max_cusp t
  obtain ⟨u, v, hu, hv, huw, hvw, huv, ht⟩ := tri_three t hw
  obtain ⟨a, b, ha, hb, h0, h1⟩ := (tri_adj hu hv huv).common_quadrant
  have hun : Unimod a b := (tri_adj hu hv huv).det ha hb
  have hwc := tri_third_cases hu hv hw huw.symm hvw.symm ha hb hun
  have hnc : ¬ (cuspN u = 1 ∧ cuspN v = 1) := fun ⟨h1, h2⟩ => hc ⟨u, v, huv, hu, hv, h1, h2⟩
  have hNu : cuspN u = N1 (a 0) (a 1) := cuspN_eq ha
  have hNv : cuspN v = N1 (b 0) (b 1) := cuspN_eq hb
  have hmaxw : cuspN w = (triRank t : ℤ) := cuspN_eq_rank hwmax
  rcases hwc with e | e
  · -- `w = ⟨a + b⟩`
    have hne : a 0 * b 0 ≠ 0 ∨ a 1 * b 1 ≠ 0 := by
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      exact hnc (by rw [hNu, hNv]; exact quadrant_central _ _ _ _ hun hcon.1 hcon.2)
    obtain ⟨g, hg⟩ := frame_minus ha hb hun
    refine ⟨⟨{u, v, minusLine hun}, g, hg⟩, ⟨?_, u, v, huv, hu, hv, by simp, by simp⟩, ?_⟩
    · intro heq
      have hwmem : w ∈ (⟨{u, v, minusLine hun}, g, hg⟩ : Tri).1 := by rw [← heq]; exact hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwmem
      rcases hwmem with e1 | e1 | e1
      · exact huw e1.symm
      · exact hvw e1.symm
      · exact plusLine_ne_minusLine hun (e.symm.trans e1)
    · have hpl : cuspN w = cuspN u + cuspN v := by
        rw [e, cuspN_plus ha hb hun h0 h1]
      have hu1 := cuspN_pos u
      have hv1 := cuspN_pos v
      have hlt := cuspN_minus_lt ha hb hun h0 h1 hne
      have hpos : 0 < triRank t := by
        have : (1 : ℤ) ≤ triRank t := by omega
        exact_mod_cast this
      show Finset.sup _ cuspNat < triRank t
      rw [Finset.sup_lt_iff (by exact hpos)]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      have key : ∀ y : RationalLine2, cuspN y < (triRank t : ℤ) → cuspNat y < triRank t := by
        intro y hy
        have : (cuspNat y : ℤ) < triRank t := by rw [cuspNat_cast]; exact hy
        exact_mod_cast this
      rcases hx with rfl | rfl | rfl
      · exact key _ (by omega)
      · exact key _ (by omega)
      · exact key _ (by omega)
  · -- `w = ⟨a - b⟩` is impossible
    exfalso
    have hw' : cuspN w = N1 (a 0 - b 0) (a 1 - b 1) := by
      rw [e, cuspN_eq (isGen_minusLine hun)]; rfl
    have hlt := N1_sub_lt_max (a 0) (a 1) (b 0) (b 1) hun h0 h1 (hNu ▸ cuspN_pos u)
      (hNv ▸ cuspN_pos v) (by rw [← hNu, ← hNv]; exact hnc)
    have h1' := cuspN_le_rank hu
    have h2' := cuspN_le_rank hv
    rw [← hNu, ← hNv] at hlt
    rw [hmaxw] at hw'
    rw [← hw'] at hlt
    omega

/-- The first coordinate vector. -/
def e1 : IntegralVector := ![1, 0]

/-- The second coordinate vector. -/
def e2 : IntegralVector := ![0, 1]

theorem e1_primitive : Primitive e1 := by simp [Primitive, content, e1]

theorem e2_primitive : Primitive e2 := by simp [Primitive, content, e2]

theorem e12_unimod : Unimod e1 e2 := by left; simp [det2, e1, e2]

/-- The cusp `⟨e₁⟩`. -/
def cusp1 : RationalLine2 := lineOf e1 e1_primitive

/-- The cusp `⟨e₂⟩`. -/
def cusp2 : RationalLine2 := lineOf e2 e2_primitive

theorem isGen_cusp1 : IsGen cusp1 e1 := isGen_lineOf _ _

theorem isGen_cusp2 : IsGen cusp2 e2 := isGen_lineOf _ _

theorem cuspN_cusp1 : cuspN cusp1 = 1 := by rw [cuspN_eq isGen_cusp1]; simp [N1, e1]

theorem cuspN_cusp2 : cuspN cusp2 = 1 := by rw [cuspN_eq isGen_cusp2]; simp [N1, e2]

theorem eq_cusp_of_cuspN_one {x : RationalLine2} (h : cuspN x = 1) : x = cusp1 ∨ x = cusp2 := by
  obtain ⟨a, ha⟩ := exists_gen x
  rw [cuspN_eq ha] at h
  unfold N1 at h
  have n0 := abs_nonneg (a 0)
  have n1 := abs_nonneg (a 1)
  have a0 : (|a 0| = 1 ∧ a 1 = 0) ∨ (|a 1| = 1 ∧ a 0 = 0) := by
    rcases (by omega : (|a 0| = 1 ∧ |a 1| = 0) ∨ (|a 0| = 0 ∧ |a 1| = 1)) with ⟨k0, k1⟩ | ⟨k0, k1⟩
    · exact Or.inl ⟨k0, abs_eq_zero.mp k1⟩
    · exact Or.inr ⟨k1, abs_eq_zero.mp k0⟩
  rcases a0 with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · left
    have : e1 = a ∨ e1 = -a := by
      rcases abs_eq (zero_le_one) |>.mp h0 with e | e
      · left; funext i; fin_cases i <;> simp [e1, e, h1]
      · right; funext i; fin_cases i <;> simp [e1, e, h1]
    exact (ha.line_eq_iff isGen_cusp1).mpr this
  · right
    have : e2 = a ∨ e2 = -a := by
      rcases abs_eq (zero_le_one) |>.mp h1 with e | e
      · left; funext i; fin_cases i <;> simp [e2, e, h0]
      · right; funext i; fin_cases i <;> simp [e2, e, h0]
    exact (ha.line_eq_iff isGen_cusp2).mpr this

theorem cusp1_ne_cusp2 : cusp1 ≠ cusp2 :=
  (Adj.of_det isGen_cusp1 isGen_cusp2 e12_unimod).1

/-- One of the two triangles over the standard edge: `{⟨e₁⟩, ⟨e₂⟩, ⟨e₁ + e₂⟩}`. -/
def triPlus : Tri :=
  ⟨{cusp1, cusp2, plusLine e12_unimod}, colGL e1 e2 e12_unimod,
    frame_plus isGen_cusp1 isGen_cusp2 e12_unimod⟩

/-- The other triangle over the standard edge: `{⟨e₁⟩, ⟨e₂⟩, ⟨e₁ - e₂⟩}`. -/
def triMinus : Tri :=
  ⟨{cusp1, cusp2, minusLine e12_unimod},
    frame_minus isGen_cusp1 isGen_cusp2 e12_unimod⟩

theorem cuspN_plus12 : cuspN (plusLine e12_unimod) = 2 := by
  rw [cuspN_plus isGen_cusp1 isGen_cusp2 e12_unimod (by simp [e1, e2]) (by simp [e1, e2]),
    cuspN_cusp1, cuspN_cusp2]; norm_num

theorem plus12_ne_cusp1 : plusLine e12_unimod ≠ cusp1 := by
  intro e; have := cuspN_plus12; rw [e, cuspN_cusp1] at this; omega

theorem plus12_ne_cusp2 : plusLine e12_unimod ≠ cusp2 := by
  intro e; have := cuspN_plus12; rw [e, cuspN_cusp2] at this; omega

theorem triPlus_ne_triMinus : triPlus ≠ triMinus := by
  intro h
  have hm : plusLine e12_unimod ∈ triMinus.1 := by
    rw [← h]; simp [triPlus]
  simp only [triMinus, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with e | e | e
  · exact plus12_ne_cusp1 e
  · exact plus12_ne_cusp2 e
  · exact plusLine_ne_minusLine e12_unimod e

theorem tAdj_triPlus_triMinus : TAdj triPlus triMinus :=
  ⟨triPlus_ne_triMinus, cusp1, cusp2, cusp1_ne_cusp2, by simp [triPlus], by simp [triPlus],
    by simp [triMinus], by simp [triMinus]⟩

theorem central_iff (t : Tri) : Central t ↔ t = triPlus ∨ t = triMinus := by
  constructor
  · rintro ⟨x, y, hxy, hx, hy, hx1, hy1⟩
    have hc1 : cusp1 ∈ t.1 ∧ cusp2 ∈ t.1 := by
      rcases eq_cusp_of_cuspN_one hx1 with rfl | rfl <;> rcases eq_cusp_of_cuspN_one hy1 with rfl | rfl
      · exact absurd rfl hxy
      · exact ⟨hx, hy⟩
      · exact ⟨hy, hx⟩
      · exact absurd rfl hxy
    obtain ⟨z, hz, hz1, hz2, htz⟩ := tri_third hc1.1 hc1.2 cusp1_ne_cusp2
    rcases tri_third_cases hc1.1 hc1.2 hz hz1 hz2 isGen_cusp1 isGen_cusp2 e12_unimod with e | e
    · left; apply Subtype.ext; rw [htz, e]; rfl
    · right; apply Subtype.ext; rw [htz, e]; rfl
  · rintro (rfl | rfl)
    · exact ⟨cusp1, cusp2, cusp1_ne_cusp2, by simp [triPlus], by simp [triPlus], cuspN_cusp1, cuspN_cusp2⟩
    · exact ⟨cusp1, cusp2, cusp1_ne_cusp2, by simp [triMinus], by simp [triMinus], cuspN_cusp1, cuspN_cusp2⟩

end TernaryPeriodPolynomials.Argument.FareyTree
