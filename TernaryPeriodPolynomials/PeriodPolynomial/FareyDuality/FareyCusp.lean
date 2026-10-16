module

public import TernaryPeriodPolynomials.Building.RankTwo.HeightLinks
public import TernaryPeriodPolynomials.Building.RankTwo.VertexLinks
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyInt

@[expose] public section


/-!
# Cusps, adjacency and triangles of the Farey complex

Formalized by Claude Sonnet 5.5.

Combinatorics of the library's `RankTwoAugmentedFrames.ambient` (the Farey complex of `RationalLine2`) through
primitive generators: `IsGen L v` ("`v` is a primitive generator of `L`", unique up to sign), `Adj L M`
(adjacent cusps, iff `det(a, b) = ±1` for generators, `adj_iff`), `Unimod a b`, the two cusps
`plusLine h = ⟨a + b⟩`, `minusLine h = ⟨a - b⟩` over the edge `⟨a⟩⟨b⟩` (every triangle on that edge has one of them
as third cusp, `third_cases`, and both give triangles, `frame_plus`, `frame_minus`), triangles `Tri` (augmented frames),
the `ℓ¹` norm of a cusp `cuspN` and the rank `triRank` of a triangle (largest norm of its cusps).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FareyTree

open TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.RankTwoVertexLinks
  TernaryPoly.RankTwoHeightLinks

/-- `v` is a primitive generator of the rational line `L`. -/
def IsGen (L : RationalLine2) (v : IntegralVector) : Prop :=
  Primitive v ∧ Submodule.span ℚ {rationalVector v} = L.val

theorem exists_gen (L : RationalLine2) : ∃ v, IsGen L v :=
  ⟨primitiveGenerator L, primitiveGenerator_primitive L, primitiveGenerator_span L⟩

theorem IsGen.primitive {L : RationalLine2} {v : IntegralVector} (h : IsGen L v) : Primitive v := h.1

theorem rationalVector_neg (v : IntegralVector) : rationalVector (-v) = -rationalVector v := by
  funext i
  simp [rationalVector]

theorem content_neg (v : IntegralVector) : content (-v) = content v := by
  simp [content, Int.gcd_neg, Int.neg_gcd]

theorem IsGen.neg {L : RationalLine2} {v : IntegralVector} (h : IsGen L v) : IsGen L (-v) := by
  refine ⟨?_, ?_⟩
  · unfold Primitive at *
    rw [content_neg]; exact h.1
  · rw [rationalVector_neg]
    have : Submodule.span ℚ {-rationalVector v} = Submodule.span ℚ {rationalVector v} := by
      apply le_antisymm
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self _)
      · rw [Submodule.span_singleton_le_iff_mem]
        have := Submodule.neg_mem (Submodule.span ℚ {-rationalVector v}) (Submodule.mem_span_singleton_self (-rationalVector v))
        simpa using this
    rw [this]; exact h.2

theorem IsGen.eq_or_neg {L : RationalLine2} {v w : IntegralVector} (hv : IsGen L v) (hw : IsGen L w) :
    w = v ∨ w = -v := by
  rcases primitive_eq_or_neg_of_span_eq hw.1 hv.1 (hw.2.trans hv.2.symm) with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem IsGen.line_eq_iff {L M : RationalLine2} {v w : IntegralVector} (hv : IsGen L v)
    (hw : IsGen M w) : L = M ↔ (w = v ∨ w = -v) := by
  constructor
  · rintro rfl; exact hv.eq_or_neg hw
  · rintro (rfl | rfl)
    · exact Subtype.ext (hv.2.symm.trans hw.2)
    · exact Subtype.ext (hv.neg.2.symm.trans hw.2)

theorem primitive_rationalVector_ne_zero {v : IntegralVector} (hp : Primitive v) :
    rationalVector v ≠ 0 := by
  intro h
  have h0 : v 0 = 0 := by
    have : (v 0 : ℚ) = 0 := congrFun h 0
    exact_mod_cast this
  have h1 : v 1 = 0 := by
    have : (v 1 : ℚ) = 0 := congrFun h 1
    exact_mod_cast this
  simp [Primitive, content, h0, h1] at hp

/-- The line spanned by a primitive vector. -/
def lineOf (v : IntegralVector) (hp : Primitive v) : RationalLine2 :=
  vectorLine (rationalVector v) (primitive_rationalVector_ne_zero hp)

theorem isGen_lineOf (v : IntegralVector) (hp : Primitive v) : IsGen (lineOf v hp) v := ⟨hp, rfl⟩

/-- The `ℓ¹` norm of a cusp, i.e. of any of its primitive generators. -/
def cuspN (L : RationalLine2) : ℤ := N1 (primitiveGenerator L 0) (primitiveGenerator L 1)

theorem cuspN_eq {L : RationalLine2} {v : IntegralVector} (h : IsGen L v) :
    cuspN L = N1 (v 0) (v 1) := by
  have hg : IsGen L (primitiveGenerator L) := ⟨primitiveGenerator_primitive L, primitiveGenerator_span L⟩
  rcases h.eq_or_neg hg with e | e
  · simp [cuspN, e]
  · simp [cuspN, e, N1]

theorem col_isGen (g : IntegralGL) (j : Fin 2) :
    IsGen (augmentedLine g j.castSucc) (fun i => g.val i j) := by
  refine ⟨column_primitive g j, ?_⟩
  change _ = Submodule.span ℚ {rationalRepresentation g (template j.castSucc)}
  rw [representation_column]

theorem col_sum_isGen (g : IntegralGL) :
    IsGen (augmentedLine g 2) (fun i => g.val i 0 + g.val i 1) := by
  have hp : Primitive (fun i => g.val i 0 + g.val i 1) := by
    refine primitive_of_bezout (a := g⁻¹.val 0 0) (b := g⁻¹.val 0 1) ?_
    have he : g⁻¹.val * g.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h0 := congrFun (congrFun he 0) 0
    have h1 := congrFun (congrFun he 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
      ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true] at h0 h1
    linarith
  refine ⟨hp, ?_⟩
  have e : rationalRepresentation g (template 2) = rationalVector (fun i => g.val i 0 + g.val i 1) := by
    rw [rationalRepresentation_apply]
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, template, rationalVector,
        Matrix.GeneralLinearGroup.map_apply]
  change _ = Submodule.span ℚ {rationalRepresentation g (template 2)}
  rw [e]

/-- Adjacency of cusps: distinct and forming an edge of the Farey complex. -/
def Adj (L M : RationalLine2) : Prop := L ≠ M ∧ ({L, M} : Finset RationalLine2) ∈ ambient

theorem det_unit_iff (g : IntegralGL) :
    det2 (g.val 0 0) (g.val 1 0) (g.val 0 1) (g.val 1 1) = 1 ∨
      det2 (g.val 0 0) (g.val 1 0) (g.val 0 1) (g.val 1 1) = -1 := by
  have h : IsUnit g.val.det := (Matrix.isUnits_det_units g)
  rcases Int.isUnit_iff.mp h with h | h
  · left; simpa [det2, Matrix.det_fin_two, mul_comm] using h
  · right; simpa [det2, Matrix.det_fin_two, mul_comm] using h

theorem det2_neg_right (a0 a1 b0 b1 : ℤ) : det2 a0 a1 (-b0) (-b1) = -det2 a0 a1 b0 b1 := by
  unfold det2; ring

theorem det2_neg_left (a0 a1 b0 b1 : ℤ) : det2 (-a0) (-a1) b0 b1 = -det2 a0 a1 b0 b1 := by
  unfold det2; ring

theorem IsGen.coords {L : RationalLine2} {a v : IntegralVector} (ha : IsGen L a) (hv : IsGen L v) :
    (a 0 = v 0 ∧ a 1 = v 1) ∨ (a 0 = -v 0 ∧ a 1 = -v 1) := by
  rcases hv.eq_or_neg ha with e | e
  · left
    exact ⟨congrFun e 0, congrFun e 1⟩
  · right
    exact ⟨congrFun e 0, congrFun e 1⟩

theorem Adj.det {L M : RationalLine2} (h : Adj L M) {a b : IntegralVector} (ha : IsGen L a)
    (hb : IsGen M b) : det2 (a 0) (a 1) (b 0) (b 1) = 1 ∨ det2 (a 0) (a 1) (b 0) (b 1) = -1 := by
  obtain ⟨g, hg0, hg1⟩ := edge_basis L M h.1 h.2
  have h0 : IsGen L (fun i => g.val i 0) := hg0 ▸ col_isGen g 0
  have h1 : IsGen M (fun i => g.val i 1) := hg1 ▸ col_isGen g 1
  have hd := det_unit_iff g
  rcases ha.coords h0 with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;> rcases hb.coords h1 with ⟨f0, f1⟩ | ⟨f0, f1⟩ <;>
  · simp only [det2] at hd ⊢
    rw [e0, e1, f0, f1]
    rcases hd with hd | hd
    · first | (left; linarith) | (right; linarith)
    · first | (left; linarith) | (right; linarith)

/-- The integral matrix with columns `a`, `b`. -/
def colMatrix (a b : IntegralVector) : Matrix (Fin 2) (Fin 2) ℤ := !![a 0, b 0; a 1, b 1]

theorem colMatrix_det (a b : IntegralVector) :
    (colMatrix a b).det = det2 (a 0) (a 1) (b 0) (b 1) := by
  simp [colMatrix, Matrix.det_fin_two, det2]
  ring

/-- The element of `GL₂(ℤ)` with columns `a`, `b` when their determinant is a unit. -/
def colGL (a b : IntegralVector) (hd : det2 (a 0) (a 1) (b 0) (b 1) = 1 ∨
    det2 (a 0) (a 1) (b 0) (b 1) = -1) : IntegralGL :=
  Matrix.nonsingInvUnit (colMatrix a b) (by
    rw [colMatrix_det]
    rcases hd with hd | hd <;> rw [hd] <;> simp)

theorem colGL_col0 (a b : IntegralVector) (hd) : (fun i => (colGL a b hd).val i 0) = a := by
  funext i; fin_cases i <;> rfl

theorem colGL_col1 (a b : IntegralVector) (hd) : (fun i => (colGL a b hd).val i 1) = b := by
  funext i; fin_cases i <;> rfl

theorem Adj.of_det {L M : RationalLine2} {a b : IntegralVector} (ha : IsGen L a) (hb : IsGen M b)
    (hd : det2 (a 0) (a 1) (b 0) (b 1) = 1 ∨ det2 (a 0) (a 1) (b 0) (b 1) = -1) : Adj L M := by
  set g := colGL a b hd with hg
  have h0 : IsGen (augmentedLine g 0) a := by
    have := col_isGen g 0
    rwa [colGL_col0] at this
  have h1 : IsGen (augmentedLine g 1) b := by
    have := col_isGen g 1
    rwa [colGL_col1] at this
  have hL : L = augmentedLine g 0 := (ha.line_eq_iff h0).mpr (Or.inl rfl)
  have hM : M = augmentedLine g 1 := (hb.line_eq_iff h1).mpr (Or.inl rfl)
  refine ⟨?_, ?_⟩
  · intro hLM
    rcases (ha.line_eq_iff hb).mp hLM with e | e
    · rcases hd with hd | hd <;> simp [det2, e] at hd <;> ring_nf at hd <;> omega
    · rcases hd with hd | hd <;> simp [det2, e] at hd <;> ring_nf at hd <;> omega
  · apply subset_augmentedFrame_mem g (Finset.insert_nonempty _ _)
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hL.symm⟩
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, hM.symm⟩

theorem adj_iff {L M : RationalLine2} {a b : IntegralVector} (ha : IsGen L a) (hb : IsGen M b) :
    Adj L M ↔ (det2 (a 0) (a 1) (b 0) (b 1) = 1 ∨ det2 (a 0) (a 1) (b 0) (b 1) = -1) :=
  ⟨fun h => h.det ha hb, Adj.of_det ha hb⟩

theorem primitive_of_det {v w : IntegralVector}
    (hd : det2 (v 0) (v 1) (w 0) (w 1) = 1 ∨ det2 (v 0) (v 1) (w 0) (w 1) = -1) : Primitive v := by
  rcases hd with hd | hd
  · exact primitive_of_bezout (a := w 1) (b := -w 0) (by simp only [det2] at hd; linarith)
  · exact primitive_of_bezout (a := -w 1) (b := w 0) (by simp only [det2] at hd; linarith)

theorem det2_comm (a0 a1 b0 b1 : ℤ) : det2 b0 b1 a0 a1 = -det2 a0 a1 b0 b1 := by
  unfold det2; ring

theorem det2_unit_symm {a0 a1 b0 b1 : ℤ} (h : det2 a0 a1 b0 b1 = 1 ∨ det2 a0 a1 b0 b1 = -1) :
    det2 b0 b1 a0 a1 = 1 ∨ det2 b0 b1 a0 a1 = -1 := by
  rw [det2_comm]; rcases h with h | h <;> rw [h] <;> simp

theorem quadrant_dichotomy (a0 a1 b0 b1 : ℤ)
    (hd : det2 a0 a1 b0 b1 = 1 ∨ det2 a0 a1 b0 b1 = -1) :
    (0 ≤ a0 * b0 ∧ 0 ≤ a1 * b1) ∨ (a0 * b0 ≤ 0 ∧ a1 * b1 ≤ 0) := by
  have h1 := unimodular_no_opposite a0 a1 b0 b1 hd
  rcases lt_trichotomy (a0 * b0) 0 with p | p | p <;> rcases lt_trichotomy (a1 * b1) 0 with q | q | q
  · exact Or.inr ⟨p.le, q.le⟩
  · exact Or.inr ⟨p.le, q.le⟩
  · exact absurd ⟨p, q⟩ h1.2
  · exact Or.inr ⟨p.le, q.le⟩
  · exact Or.inl ⟨p.ge, q.ge⟩
  · exact Or.inl ⟨p.ge, q.le⟩
  · exact absurd ⟨p, q⟩ h1.1
  · exact Or.inl ⟨p.le, q.ge⟩
  · exact Or.inl ⟨p.le, q.le⟩

/-- Two adjacent cusps have generators in a common closed quadrant. -/
theorem Adj.common_quadrant {x y : RationalLine2} (h : Adj x y) :
    ∃ a b : IntegralVector, IsGen x a ∧ IsGen y b ∧ 0 ≤ a 0 * b 0 ∧ 0 ≤ a 1 * b 1 := by
  obtain ⟨a, ha⟩ := exists_gen x
  obtain ⟨b, hb⟩ := exists_gen y
  rcases quadrant_dichotomy (a 0) (a 1) (b 0) (b 1) (h.det ha hb) with k | k
  · exact ⟨a, b, ha, hb, k.1, k.2⟩
  · exact ⟨a, -b, ha, hb.neg, by simpa using k.1, by simpa using k.2⟩

/-- A unimodular pair of integral vectors. -/
def Unimod (a b : IntegralVector) : Prop :=
  det2 (a 0) (a 1) (b 0) (b 1) = 1 ∨ det2 (a 0) (a 1) (b 0) (b 1) = -1

theorem Unimod.symm {a b : IntegralVector} (h : Unimod a b) : Unimod b a := det2_unit_symm h

theorem Unimod.primitive_left {a b : IntegralVector} (h : Unimod a b) : Primitive a :=
  primitive_of_det h

theorem Unimod.primitive_right {a b : IntegralVector} (h : Unimod a b) : Primitive b :=
  primitive_of_det h.symm

theorem Unimod.add_left {a b : IntegralVector} (h : Unimod a b) : Unimod (a + b) b := by
  unfold Unimod det2 at *
  simp only [Pi.add_apply]
  rcases h with h | h
  · left; linarith
  · right; linarith

theorem Unimod.sub_left {a b : IntegralVector} (h : Unimod a b) : Unimod (a - b) b := by
  unfold Unimod det2 at *
  simp only [Pi.sub_apply]
  rcases h with h | h
  · left; linarith
  · right; linarith

theorem Unimod.neg_right {a b : IntegralVector} (h : Unimod a b) : Unimod a (-b) := by
  unfold Unimod det2 at *
  simp only [Pi.neg_apply]
  rcases h with h | h
  · right; linarith
  · left; linarith

/-- The cusp `⟨a + b⟩` over the edge `⟨a⟩⟨b⟩`. -/
def plusLine {a b : IntegralVector} (h : Unimod a b) : RationalLine2 :=
  lineOf (a + b) h.add_left.primitive_left

/-- The cusp `⟨a - b⟩` over the edge `⟨a⟩⟨b⟩`. -/
def minusLine {a b : IntegralVector} (h : Unimod a b) : RationalLine2 :=
  lineOf (a - b) h.sub_left.primitive_left

theorem isGen_plusLine {a b : IntegralVector} (h : Unimod a b) : IsGen (plusLine h) (a + b) :=
  isGen_lineOf _ _

theorem isGen_minusLine {a b : IntegralVector} (h : Unimod a b) : IsGen (minusLine h) (a - b) :=
  isGen_lineOf _ _

theorem plusLine_ne_minusLine {a b : IntegralVector} (h : Unimod a b) :
    plusLine h ≠ minusLine h := by
  intro e
  rcases (isGen_plusLine h).line_eq_iff (isGen_minusLine h) |>.mp e with e | e
  · have h0 := congrFun e 0
    have h1 := congrFun e 1
    simp only [Pi.sub_apply, Pi.add_apply] at h0 h1
    have e0 : b 0 = 0 := by linarith
    have e1 : b 1 = 0 := by linarith
    rcases h with h | h <;> simp only [det2] at h <;> simp [e0, e1] at h
  · have h0 := congrFun e 0
    have h1 := congrFun e 1
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at h0 h1
    have : a 0 = 0 := by linarith
    have : a 1 = 0 := by linarith
    rcases h with h | h <;> simp only [det2] at h <;> simp [*] at h

theorem Adj.symm {L M : RationalLine2} (h : Adj L M) : Adj M L :=
  ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩

/-- Triangles of the Farey complex: the augmented frames. -/
def Tri : Type := {s : Finset RationalLine2 // ∃ g : IntegralGL, s = augmentedFrame g}

theorem mem_frame {g : IntegralGL} {x : RationalLine2} :
    x ∈ augmentedFrame g ↔ x = augmentedLine g 0 ∨ x = augmentedLine g 1 ∨ x = augmentedLine g 2 := by
  unfold augmentedFrame
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem frame_adj {g : IntegralGL} {x y : RationalLine2} (hx : x ∈ augmentedFrame g)
    (hy : y ∈ augmentedFrame g) (hxy : x ≠ y) : Adj x y := by
  have g0 : IsGen (augmentedLine g 0) (fun i => g.val i 0) := col_isGen g 0
  have g1 : IsGen (augmentedLine g 1) (fun i => g.val i 1) := col_isGen g 1
  have g2 := col_sum_isGen g
  have hd := det_unit_iff g
  rw [mem_frame] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals try exact absurd rfl hxy
  · exact Adj.of_det g0 g1 hd
  · refine Adj.of_det g0 g2 ?_
    simp only [det2] at hd ⊢
    rcases hd with hd | hd
    · left; linarith
    · right; linarith
  · exact (Adj.of_det g0 g1 hd).symm
  · refine Adj.of_det g1 g2 ?_
    simp only [det2] at hd ⊢
    rcases hd with hd | hd
    · right; linarith
    · left; linarith
  · refine (Adj.of_det g0 g2 ?_).symm
    simp only [det2] at hd ⊢
    rcases hd with hd | hd
    · left; linarith
    · right; linarith
  · refine (Adj.of_det g1 g2 ?_).symm
    simp only [det2] at hd ⊢
    rcases hd with hd | hd
    · right; linarith
    · left; linarith

theorem frame_card (g : IntegralGL) : (augmentedFrame g).card = 3 := augmentedFrame_card g

theorem exists_third {g : IntegralGL} {x y : RationalLine2} (hx : x ∈ augmentedFrame g)
    (hy : y ∈ augmentedFrame g) (hxy : x ≠ y) :
    ∃ z, z ∈ augmentedFrame g ∧ z ≠ x ∧ z ≠ y ∧ augmentedFrame g = {x, y, z} := by
  classical
  have hcard : ((augmentedFrame g).erase x |>.erase y).card = 1 := by
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem hx, frame_card]
    rw [Finset.mem_erase]; exact ⟨hxy.symm, hy⟩
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hzmem : z ∈ ((augmentedFrame g).erase x |>.erase y) := by rw [hz]; simp
  simp only [Finset.mem_erase] at hzmem
  obtain ⟨hzy, hzx, hzg⟩ := hzmem
  refine ⟨z, hzg, hzx, hzy, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  · rw [frame_card]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
    · simp
    · simpa using hzy.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, hzx.symm⟩

/-- Plücker identity: a third generator is a signed sum of two generators of an edge. -/
theorem pluecker {a b c : IntegralVector} (hab : Unimod a b) (hcb : Unimod c b) (hac : Unimod a c) :
    (c = a + b ∨ c = a - b ∨ c = -a + b ∨ c = -a - b) := by
  have key : ∀ i : Fin 2, det2 (a 0) (a 1) (b 0) (b 1) * c i =
      det2 (c 0) (c 1) (b 0) (b 1) * a i + det2 (a 0) (a 1) (c 0) (c 1) * b i := by
    intro i; fin_cases i <;> simp [det2] <;> ring
  unfold Unimod at hab hcb hac
  have e0 := key 0
  have e1 := key 1
  rcases hab with h1 | h1 <;> rcases hcb with h2 | h2 <;> rcases hac with h3 | h3 <;>
  rw [h1, h2, h3] at e0 e1 <;>
  first
  | (left; funext i; fin_cases i <;> simp <;> linarith)
  | (right; left; funext i; fin_cases i <;> simp <;> linarith)
  | (right; right; left; funext i; fin_cases i <;> simp <;> linarith)
  | (right; right; right; funext i; fin_cases i <;> simp <;> linarith)

theorem third_cases {g : IntegralGL} {x y z : RationalLine2} (hx : x ∈ augmentedFrame g)
    (hy : y ∈ augmentedFrame g) (hz : z ∈ augmentedFrame g) (hzx : z ≠ x)
    (hzy : z ≠ y) {a b : IntegralVector} (ha : IsGen x a) (hb : IsGen y b) (h : Unimod a b) :
    z = plusLine h ∨ z = minusLine h := by
  obtain ⟨c, hc⟩ := exists_gen z
  have hcb : Unimod c b := (frame_adj hz hy hzy).det hc hb
  have hac : Unimod a c := (frame_adj hx hz hzx.symm).det ha hc
  rcases pluecker h hcb hac with e | e | e | e
  · left
    exact ((isGen_plusLine h).line_eq_iff hc).mpr (Or.inl e) |>.symm
  · right
    exact ((isGen_minusLine h).line_eq_iff hc).mpr (Or.inl e) |>.symm
  · right
    refine ((isGen_minusLine h).line_eq_iff hc).mpr (Or.inr ?_) |>.symm
    rw [e]; abel
  · left
    refine ((isGen_plusLine h).line_eq_iff hc).mpr (Or.inr ?_) |>.symm
    rw [e]; abel

theorem frame_plus {x y : RationalLine2} {a b : IntegralVector} (ha : IsGen x a) (hb : IsGen y b)
    (h : Unimod a b) : ({x, y, plusLine h} : Finset RationalLine2) = augmentedFrame (colGL a b h) := by
  generalize hg : colGL a b h = g
  have c0 : (fun i => g.val i 0) = a := hg ▸ colGL_col0 a b h
  have c1 : (fun i => g.val i 1) = b := hg ▸ colGL_col1 a b h
  have g0 : IsGen (augmentedLine g 0) a := by
    have := col_isGen g 0; rwa [c0] at this
  have g1 : IsGen (augmentedLine g 1) b := by
    have := col_isGen g 1; rwa [c1] at this
  have g2 : IsGen (augmentedLine g 2) (a + b) := by
    have := col_sum_isGen g
    convert this using 1
    funext i
    have e0 := congrFun c0 i
    have e1 := congrFun c1 i
    simp only [Pi.add_apply]
    rw [e0, e1]
  have ex : x = augmentedLine g 0 := (ha.line_eq_iff g0).mpr (Or.inl rfl)
  have ey : y = augmentedLine g 1 := (hb.line_eq_iff g1).mpr (Or.inl rfl)
  have ez : plusLine h = augmentedLine g 2 := ((isGen_plusLine h).line_eq_iff g2).mpr (Or.inl rfl)
  ext w
  rw [mem_frame, ← ex, ← ey, ← ez]
  simp

theorem frame_minus_eq {x y : RationalLine2} {a b : IntegralVector} (ha : IsGen x a) (hb : IsGen y b)
    (h : Unimod a b) :
    ({x, y, minusLine h} : Finset RationalLine2) = augmentedFrame (colGL a (-b) h.neg_right) := by
  have h' : Unimod a (-b) := h.neg_right
  generalize hg : colGL a (-b) h' = g
  have c0 : (fun i => g.val i 0) = a := hg ▸ colGL_col0 a (-b) h'
  have c1 : (fun i => g.val i 1) = -b := hg ▸ colGL_col1 a (-b) h'
  have hb' : IsGen y (-b) := hb.neg
  have g0 : IsGen (augmentedLine g 0) a := by
    have := col_isGen g 0; rwa [c0] at this
  have g1 : IsGen (augmentedLine g 1) (-b) := by
    have := col_isGen g 1; rwa [c1] at this
  have g2 : IsGen (augmentedLine g 2) (a - b) := by
    have := col_sum_isGen g
    convert this using 1
    funext i
    have e0 := congrFun c0 i
    have e1 := congrFun c1 i
    simp only [Pi.sub_apply]
    rw [e0, e1]
    simp [sub_eq_add_neg]
  have ex : x = augmentedLine g 0 := (ha.line_eq_iff g0).mpr (Or.inl rfl)
  have ey : y = augmentedLine g 1 := (hb'.line_eq_iff g1).mpr (Or.inl rfl)
  have ez : minusLine h = augmentedLine g 2 := ((isGen_minusLine h).line_eq_iff g2).mpr (Or.inl rfl)
  ext w
  rw [mem_frame, ← ex, ← ey, ← ez]
  simp

theorem frame_minus {x y : RationalLine2} {a b : IntegralVector} (ha : IsGen x a) (hb : IsGen y b)
    (h : Unimod a b) :
    ∃ g : IntegralGL, ({x, y, minusLine h} : Finset RationalLine2) = augmentedFrame g :=
  ⟨_, frame_minus_eq ha hb h⟩

theorem N1_pos_of_primitive {v : IntegralVector} (hp : Primitive v) : 1 ≤ N1 (v 0) (v 1) := by
  by_contra hcon
  have ha := abs_nonneg (v 0)
  have hb := abs_nonneg (v 1)
  unfold N1 at hcon
  have h0 : v 0 = 0 := abs_eq_zero.mp (by omega)
  have h1 : v 1 = 0 := abs_eq_zero.mp (by omega)
  simp [Primitive, content, h0, h1] at hp

theorem cuspN_pos (L : RationalLine2) : 1 ≤ cuspN L := by
  obtain ⟨v, hv⟩ := exists_gen L
  rw [cuspN_eq hv]
  exact N1_pos_of_primitive hv.primitive

/-- The norm of a cusp as a natural number. -/
def cuspNat (L : RationalLine2) : ℕ := (cuspN L).toNat

theorem cuspNat_cast (L : RationalLine2) : (cuspNat L : ℤ) = cuspN L :=
  Int.toNat_of_nonneg (by linarith [cuspN_pos L])

/-- The rank of a triangle: the largest norm of its cusps. -/
def triRank (t : Tri) : ℕ := t.1.sup cuspNat

theorem le_triRank {t : Tri} {x : RationalLine2} (hx : x ∈ t.1) : cuspNat x ≤ triRank t :=
  Finset.le_sup (f := cuspNat) hx

theorem exists_max_cusp (t : Tri) : ∃ w ∈ t.1, cuspNat w = triRank t := by
  obtain ⟨g, hg⟩ := t.2
  have hne : t.1.Nonempty := by rw [hg]; exact Finset.card_pos.mp (by rw [frame_card]; norm_num)
  exact Finset.exists_mem_eq_sup t.1 hne cuspNat |>.imp fun w hw => ⟨hw.1, hw.2.symm⟩

theorem triRank_le {t : Tri} {n : ℕ} (h : ∀ x ∈ t.1, cuspNat x ≤ n) : triRank t ≤ n :=
  Finset.sup_le h

end TernaryPeriodPolynomials.Argument.FareyTree
