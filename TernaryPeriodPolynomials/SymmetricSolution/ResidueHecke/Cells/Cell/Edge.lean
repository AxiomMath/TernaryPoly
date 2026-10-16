module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Farey
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyEdge

@[expose] public section


/-!
# Lemma B.1, boundary route: the classes of the oriented edges of the dual Farey tree in `Φ(RG_3)`

For an oriented edge `e = (t, t')` of the dual Farey tree (two adjacent triangles), let `x, y` be the lines of the common
edge and `z` the third line of `t`, with generators `a, b, c`.  The class `K3 a b c = sign(ob a b c) [(e₀, a, b)]` of the
top cell over the common edge, oriented by the third vertex of `t`, depends only on `e` (`F3`), is antisymmetric under
the reversal of `e`, is equivariant with the determinant twist, and has boundary `F2 t' - F2 t` in `Φ(RG_2)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Finsupp TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract TernaryPoly.RankTwoAugmentedFrames
  TernaryPeriodPolynomials.Argument.FareyTree

/-- The class of the top cell over the edge `(a, b)` oriented by the third vertex `c`. -/
def K3 (a b c : IntegralVector) : (PhiX 3).V :=
  ((Int.sign (ob a b c) : ℤ) : ℚ) • Eg a b

theorem K3_neg_left (a b c : IntegralVector) : K3 (-a) b c = K3 a b c := by
  unfold K3; rw [ob_neg_left, Eg_neg_left]

theorem K3_neg_mid (a b c : IntegralVector) : K3 a (-b) c = K3 a b c := by
  unfold K3; rw [ob_neg_mid, Eg_neg_right]

theorem K3_neg_right (a b c : IntegralVector) : K3 a b (-c) = K3 a b c := by
  unfold K3; rw [ob_neg_right]

theorem K3_swap (a b c : IntegralVector) : K3 b a c = K3 a b c := by
  unfold K3
  rw [ob_swap01, Int.sign_neg, Eg_swap]
  simp

theorem K3_of_pm {a a' b b' c c' : IntegralVector} (ha : a' = a ∨ a' = -a) (hb : b' = b ∨ b' = -b)
    (hc : c' = c ∨ c' = -c) : K3 a' b' c' = K3 a b c := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp only [K3_neg_left, K3_neg_mid, K3_neg_right]

/-- `(a, b, c)` are generators of the common edge of an oriented edge and of the third line of its source. -/
def EdgeGens (e : OTE) (a b c : IntegralVector) : Prop :=
  ∃ x y z : RationalLine2, x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ e.1.1.1 = {x, y, z} ∧ x ∈ e.1.2.1 ∧ y ∈ e.1.2.1 ∧
    IsGen x a ∧ IsGen y b ∧ IsGen z c

theorem exists_edgeGens (e : OTE) : ∃ a b c, EdgeGens e a b c := by
  obtain ⟨hne, x, y, hxy, hx, hy, hx', hy'⟩ := e.2
  obtain ⟨z, hz, hzx, hzy, hzeq⟩ := tri_third hx hy hxy
  obtain ⟨a, ha⟩ := exists_gen x
  obtain ⟨b, hb⟩ := exists_gen y
  obtain ⟨c, hc⟩ := exists_gen z
  exact ⟨a, b, c, x, y, z, hxy, hzx, hzy, hzeq, hx', hy', ha, hb, hc⟩

theorem tri_card (t : Tri) : t.1.card = 3 := by
  obtain ⟨g, hg⟩ := t.2
  rw [hg]; exact augmentedFrame_card g

theorem K3_eq_of_edgeGens {e : OTE} {a b c a' b' c' : IntegralVector} (h : EdgeGens e a b c)
    (h' : EdgeGens e a' b' c') : K3 a' b' c' = K3 a b c := by
  obtain ⟨x, y, z, hxy, hzx, hzy, ht, hx, hy, ha, hb, hc⟩ := h
  obtain ⟨x', y', z', hxy', hzx', hzy', ht', hx', hy', ha', hb', hc'⟩ := h'
  -- the third line of the source is not in the target
  have hznot : z ∉ e.1.2.1 := by
    intro hz
    have hsub : ({x, y, z} : Finset RationalLine2) ⊆ e.1.2.1 := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have hcard : ({x, y, z} : Finset RationalLine2).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hzx.symm]),
        Finset.card_insert_of_notMem (by simp [hzy.symm]), Finset.card_singleton]
    have : e.1.2.1 = {x, y, z} :=
      (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, tri_card])).symm
    exact e.2.1 (Subtype.ext (ht.trans this.symm))
  have hmem : ∀ w, w ∈ e.1.1.1 → w ∈ e.1.2.1 → w = x ∨ w = y := by
    intro w hw1 hw2
    rw [ht] at hw1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw1
    rcases hw1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd (h1 ▸ hw2) hznot
  have hx'1 : x' ∈ e.1.1.1 := by rw [ht']; simp
  have hy'1 : y' ∈ e.1.1.1 := by rw [ht']; simp
  have hz'1 : z' ∈ ({x, y, z} : Finset RationalLine2) := by rw [← ht, ht']; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz'1
  rcases hmem x' hx'1 hx' with hxx | hxx <;> rcases hmem y' hy'1 hy' with hyy | hyy
  · exact absurd (hxx.trans hyy.symm) hxy'
  · -- (x', y') = (x, y)
    have hzz : z' = z := by
      rcases hz'1 with h1 | h1 | h1
      · exact absurd (h1.trans hxx.symm) hzx'
      · exact absurd (h1.trans hyy.symm) hzy'
      · exact h1
    rw [hxx] at ha'
    rw [hyy] at hb'
    rw [hzz] at hc'
    exact K3_of_pm (ha.eq_or_neg ha') (hb.eq_or_neg hb') (hc.eq_or_neg hc')
  · -- (x', y') = (y, x)
    have hzz : z' = z := by
      rcases hz'1 with h1 | h1 | h1
      · exact absurd (h1.trans hyy.symm) hzy'
      · exact absurd (h1.trans hxx.symm) hzx'
      · exact h1
    rw [hxx] at ha'
    rw [hyy] at hb'
    rw [hzz] at hc'
    rw [K3_of_pm (hb.eq_or_neg ha') (ha.eq_or_neg hb') (hc.eq_or_neg hc'), K3_swap]
  · exact absurd (hxx.trans hyy.symm) hxy'

/-- The class of an oriented edge in `Φ(RG_3)`. -/
def F3 (e : OTE) : (PhiX 3).V :=
  K3 (Classical.choose (exists_edgeGens e)) (Classical.choose (Classical.choose_spec (exists_edgeGens e)))
    (Classical.choose (Classical.choose_spec (Classical.choose_spec (exists_edgeGens e))))

theorem F3_eq {e : OTE} {a b c : IntegralVector} (h : EdgeGens e a b c) : F3 e = K3 a b c :=
  K3_eq_of_edgeGens h (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (exists_edgeGens e))))

theorem isGen_smul (C : GL2Z) {L : RationalLine2} {v : IntegralVector} (h : IsGen L v) :
    IsGen (C • L) (C.val.mulVec v) := by
  obtain ⟨g, hg⟩ := rationalLine_eq_augmentedLine L
  subst hg
  have h0 : IsGen (augmentedLine g 0) (fun i => g.val i 0) := col_isGen g 0
  have hC : IsGen (C • augmentedLine g 0) (fun i => (C * g).val i 0) := by
    rw [smul_augmentedLine]
    exact col_isGen (C * g) 0
  have hmul : (fun i => (C * g).val i 0) = C.val.mulVec (fun i => g.val i 0) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
  rcases h0.eq_or_neg h with e | e
  · rw [e, ← hmul]; exact hC
  · rw [e, Matrix.mulVec_neg, ← hmul]; exact hC.neg

theorem EdgeGens.smul {e : OTE} {a b c : IntegralVector} (h : EdgeGens e a b c) (C : GL2Z) :
    EdgeGens (C • e) (C.val.mulVec a) (C.val.mulVec b) (C.val.mulVec c) := by
  obtain ⟨x, y, z, hxy, hzx, hzy, ht, hx, hy, ha, hb, hc⟩ := h
  refine ⟨C • x, C • y, C • z, fun e' => hxy (MulAction.injective C e'),
    fun e' => hzx (MulAction.injective C e'), fun e' => hzy (MulAction.injective C e'), ?_, ?_, ?_,
    isGen_smul C ha, isGen_smul C hb, isGen_smul C hc⟩
  · change (C • e.1.1).1 = _
    rw [tri_smul_val, ht]
    simp [Finset.image_insert]
  · exact smul_mem_tri_smul hx
  · exact smul_mem_tri_smul hy

theorem Eg_act (g : PH) (a b : IntegralVector) :
    (PhiX 3).ρ (QuotientGroup.mk g) (Eg a b) = Eg ((pi g).val.mulVec a) ((pi g).val.mulVec b) := by
  unfold Eg
  have hm : ∀ i : Fin 2, ∃ y, (![pl a, pl b] : Fin 2 → Line) i = pl y := by
    intro i; fin_cases i
    · exact ⟨a, rfl⟩
    · exact ⟨b, rfl⟩
  have := phi_twist_cons_e0_full g (n := 3) ![pl a, pl b] hm
  have hR : (Fin.cons e0L (fun i => g.1 • (![pl a, pl b] : Fin 2 → Line) i) : Fin 3 → Line) =
      ![e0L, pl ((pi g).val.mulVec a), pl ((pi g).val.mulVec b)] := by
    funext i
    fin_cases i
    · rfl
    · exact PH_smul_pl g a
    · exact PH_smul_pl g b
  rw [hR] at this
  exact this

theorem K3_act (g : PH) (a b c : IntegralVector) :
    (PhiX 3).ρ (QuotientGroup.mk g) (K3 a b c) =
      (((pi g).val.det : ℤ) : ℚ) • K3 ((pi g).val.mulVec a) ((pi g).val.mulVec b) ((pi g).val.mulVec c) := by
  unfold K3
  rw [map_smul, Eg_act, smul_smul, ob_mulVec, sign_det_mul _ _ (det_pm (pi g))]
  congr 1
  rcases det_pm (pi g) with h | h <;> simp [h]

theorem F3_act (g : PH) (e : OTE) :
    (PhiX 3).ρ (QuotientGroup.mk g) (F3 e) = (((pi g).val.det : ℤ) : ℚ) • F3 ((pi g) • e) := by
  obtain ⟨a, b, c, h⟩ := exists_edgeGens e
  rw [F3_eq h, F3_eq (h.smul (pi g)), K3_act]

theorem edgeGens_p0 : EdgeGens p0 e1 e2 (e1 + e2) := by
  refine ⟨cusp1, cusp2, plusLine e12_unimod, cusp1_ne_cusp2, plus12_ne_cusp1, plus12_ne_cusp2, ?_, ?_, ?_,
    isGen_cusp1, isGen_cusp2, isGen_plusLine e12_unimod⟩
  · rfl
  · change cusp1 ∈ triMinus.1
    simp [triMinus]
  · change cusp2 ∈ triMinus.1
    simp [triMinus]

theorem ob_e12 : ob e1 e2 (e1 + e2) = 1 := by
  simp [ob, D2, e1, e2]

theorem F3_p0 : F3 p0 = Eg e1 e2 := by
  rw [F3_eq edgeGens_p0]
  unfold K3
  rw [ob_e12]
  simp

theorem Eg_e12 : Eg e1 e2 = clsU 3 (tupleVec 3 T3t) := by
  unfold Eg T3t p1 p2
  rfl

theorem F2_triPlus : F2 triPlus = G2 ![e1, e2, e1 + e2] := by
  have : triPlus = triOf 1 := Subtype.ext (by rw [triPlus_val]; rfl)
  rw [this, F2_frame]
  congr 1
  funext i
  fin_cases i <;> (funext j; fin_cases j <;> simp [frameVecs, e1, e2])

theorem F2_triMinus : F2 triMinus = G2 ![e1, -e2, e1 - e2] := by
  have : triMinus = triOf sOne := Subtype.ext (by rw [triMinus_val]; rfl)
  rw [this, F2_frame]
  congr 1
  funext i
  fin_cases i <;> (funext j; fin_cases j <;> simp [frameVecs, sOne, colGL_val_zero, colGL_val_one, e1, e2])

theorem tupleVec_swap {n k : ℕ} (ℓ : Fin k → Line) (i j : Fin k) (hij : i ≠ j) :
    tupleVec n (fun m => ℓ (Equiv.swap i j m)) = - tupleVec n ℓ := by
  by_cases hok : TupleOK n ℓ
  · rw [tupleVec_perm hok, Equiv.Perm.sign_swap hij]
    simp
  · have : ¬ TupleOK n (fun m => ℓ (Equiv.swap i j m)) := fun h => hok ((TupleOK.perm_iff _ _).mp h)
    rw [tupleVec_of_not_ok hok, tupleVec_of_not_ok this, neg_zero]

theorem tupleVec_swap01 (n : ℕ) (w u : Line) {k : ℕ} (m : Fin k → Line) :
    tupleVec n (Fin.cons w (Fin.cons u m : Fin (k + 1) → Line) : Fin (k + 2) → Line) =
      - tupleVec n (Fin.cons u (Fin.cons w m : Fin (k + 1) → Line) : Fin (k + 2) → Line) := by
  have h := tupleVec_swap (n := n) (Fin.cons w (Fin.cons u m : Fin (k + 1) → Line) : Fin (k + 2) → Line) 0 1
    (by simp)
  have e : (fun p => (Fin.cons w (Fin.cons u m : Fin (k + 1) → Line) : Fin (k + 2) → Line)
      (Equiv.swap (0 : Fin (k + 2)) 1 p)) =
      (Fin.cons u (Fin.cons w m : Fin (k + 1) → Line) : Fin (k + 2) → Line) := by
    funext p
    refine Fin.cases ?_ (fun q => ?_) p
    · rw [Equiv.swap_apply_left]; simp
    · refine Fin.cases ?_ (fun r => ?_) q
      · rw [show (Fin.succ (0 : Fin (k + 1)) : Fin (k + 2)) = 1 from Fin.succ_zero_eq_one, Equiv.swap_apply_right]
        simp
      · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (by
          intro h
          have h' : (r.succ).succ = (0 : Fin (k + 1)).succ := by
            rw [Fin.succ_zero_eq_one]; exact h
          exact Fin.succ_ne_zero _ (Fin.succ_injective _ h'))]
        simp
  rw [e] at h
  rw [h]; simp

theorem tupleVec_rot (n : ℕ) (u v w : Line) :
    tupleVec n (![e0L, v, w, u] : Fin 4 → Line) = tupleVec n (![e0L, u, v, w] : Fin 4 → Line) := by
  have h1 := tupleVec_swap (n := n) (![e0L, u, v, w] : Fin 4 → Line) 1 2 (by decide)
  have h2 := tupleVec_swap (n := n)
    (fun m => (![e0L, u, v, w] : Fin 4 → Line) (Equiv.swap (1 : Fin 4) 2 m)) 2 3 (by decide)
  have e : (fun p => (fun m => (![e0L, u, v, w] : Fin 4 → Line) (Equiv.swap (1 : Fin 4) 2 m))
      (Equiv.swap (2 : Fin 4) 3 p)) = (![e0L, v, w, u] : Fin 4 → Line) := by
    funext p
    fin_cases p <;> simp [Equiv.swap_apply_def]
  rw [e] at h2
  rw [h2, h1]; simp

theorem clsU_neg (n : ℕ) (v : Graded n →₀ ℚ) : clsU n (-v) = - clsU n v :=
  map_neg (Representation.Coinvariants.mk ((RGXph n).ρ.comp U.subtype)) v

theorem G2_triPlus_expand : G2 ![e1, e2, e1 + e2] =
    clsU 2 (tupleVec 2 (![e0L, p1, p2, pl ![1, 1]] : Fin 4 → Line)) := by
  unfold G2
  have hob : Int.sign (ob (![e1, e2, e1 + e2] 0) (![e1, e2, e1 + e2] 1) (![e1, e2, e1 + e2] 2)) = 1 := by
    show Int.sign (ob e1 e2 (e1 + e2)) = 1
    rw [ob_e12]; rfl
  have htup : (Fin.cons e0L (fun i => pl (![e1, e2, e1 + e2] i)) : Fin 4 → Line) =
      ![e0L, p1, p2, pl ![1, 1]] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · show pl (e1 + e2) = pl ![1, 1]
      congr 1; funext j; fin_cases j <;> simp [e1, e2]
  rw [hob, htup]; simp

theorem G2_triMinus_expand : G2 ![e1, -e2, e1 - e2] =
    - clsU 2 (tupleVec 2 (![e0L, p1, p2, pl ![1, -1]] : Fin 4 → Line)) := by
  unfold G2
  have hob : Int.sign (ob (![e1, -e2, e1 - e2] 0) (![e1, -e2, e1 - e2] 1) (![e1, -e2, e1 - e2] 2)) = -1 := by
    show Int.sign (ob e1 (-e2) (e1 - e2)) = -1
    have : ob e1 (-e2) (e1 - e2) = -1 := by simp [ob, D2, e1, e2]
    rw [this]; rfl
  have htup : (Fin.cons e0L (fun i => pl (![e1, -e2, e1 - e2] i)) : Fin 4 → Line) =
      ![e0L, p1, p2, pl ![1, -1]] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · show pl (-e2) = pl ![0, 1]
      rw [pl_eq_iff]; right; funext j; fin_cases j <;> simp [e2]
    · show pl (e1 - e2) = pl ![1, -1]
      congr 1; funext j; fin_cases j <;> simp [e1, e2]
  rw [hob, htup]; simp

theorem tupleVec_cons_T3t (w : Line) :
    tupleVec 2 (Fin.cons w T3t : Fin 4 → Line) = - tupleVec 2 (![e0L, p1, p2, w] : Fin 4 → Line) := by
  have h1 := tupleVec_swap01 2 w e0L ![p1, p2]
  have h2 := tupleVec_rot 2 w p1 p2
  have e1' : (Fin.cons w T3t : Fin 4 → Line) = Fin.cons w (Fin.cons e0L ![p1, p2] : Fin 3 → Line) := rfl
  rw [e1', h1]
  have e2' : (Fin.cons e0L (Fin.cons w ![p1, p2] : Fin 3 → Line) : Fin 4 → Line) = ![e0L, w, p1, p2] := rfl
  rw [e2', ← h2]

/-- **The boundary of the standard edge class.** -/
theorem F3_boundary_p0 :
    ((TernaryPeriodPolynomials.Argument.HochschildSerre.Phi U).map
      ((Rep.resFunctor PH.subtype).map (dRG 2))).hom (F3 p0) = F2 triMinus - F2 triPlus := by
  rw [F3_p0, Eg_e12, phi_d 2, phi_d_T3t, F2_triPlus, F2_triMinus, G2_triPlus_expand, G2_triMinus_expand,
    tupleVec_cons_T3t, tupleVec_cons_T3t, clsU_neg, clsU_neg]
  abel

/-- The boundary of `Φ(RG)`. -/
def dPhi (n : ℕ) : PhiX (n + 1) ⟶ PhiX n :=
  (TernaryPeriodPolynomials.Argument.HochschildSerre.Phi U).map ((Rep.resFunctor PH.subtype).map (dRG n))

theorem dPhi_act (n : ℕ) (q : PH ⧸ U) (x : (PhiX (n + 1)).V) :
    (dPhi n).hom ((PhiX (n + 1)).ρ q x) = (PhiX n).ρ q ((dPhi n).hom x) :=
  Rep.hom_comm_apply (dPhi n) q x

theorem F3_smul_eq (c : PH) (p : OTE) :
    F3 ((pi c) • p) = (((pi c).val.det : ℤ) : ℚ) • (PhiX 3).ρ (QuotientGroup.mk c) (F3 p) := by
  rw [F3_act, smul_smul]
  have : (((pi c).val.det : ℤ) : ℚ) * (((pi c).val.det : ℤ) : ℚ) = 1 := by
    rcases det_pm (pi c) with h | h <;> simp [h]
  rw [this, one_smul]

theorem F2_smul_eq (c : PH) (t : Tri) :
    F2 ((pi c) • t) = (((pi c).val.det : ℤ) : ℚ) • (PhiX 2).ρ (QuotientGroup.mk c) (F2 t) := by
  rw [F2_act, smul_smul]
  have : (((pi c).val.det : ℤ) : ℚ) * (((pi c).val.det : ℤ) : ℚ) = 1 := by
    rcases det_pm (pi c) with h | h <;> simp [h]
  rw [this, one_smul]

/-- **The boundary of the class of an oriented edge**: `F2 t' - F2 t`. -/
theorem F3_boundary (e : OTE) : (dPhi 2).hom (F3 e) = F2 e.1.2 - F2 e.1.1 := by
  obtain ⟨g, rfl⟩ := ote_transitive e
  obtain ⟨c, hc⟩ := pi_surjective g
  rw [← hc, F3_smul_eq, map_smul, dPhi_act]
  have h0 : (dPhi 2).hom (F3 p0) = F2 triMinus - F2 triPlus := F3_boundary_p0
  rw [h0, map_sub]
  show _ = F2 (pi c • triMinus) - F2 (pi c • triPlus)
  rw [F2_smul_eq c triMinus, F2_smul_eq c triPlus, smul_sub]

theorem sOne_val0 (i : Fin 2) : sOne.val i 0 = e1 i := colGL_val_zero _ _ _ i

theorem sOne_val1 (i : Fin 2) : sOne.val i 1 = (-e2) i := colGL_val_one _ _ _ i

theorem sOne_det : (sOne.val.det : ℤ) = -1 := by
  have h : sOne.val = colMatrix e1 (-e2) := rfl
  rw [h, colMatrix_det]
  simp [det2, e1, e2]

theorem F3_smul_swap (p : OTE) : F3 p.swap = - F3 p := by
  obtain ⟨g, rfl⟩ := ote_transitive p
  obtain ⟨c, hc⟩ := pi_surjective g
  rw [OTE.swap_smul, ← hc, F3_smul_eq, F3_smul_eq]
  have h : F3 p0.swap = - F3 p0 := by
    obtain ⟨s, hs⟩ := pi_surjective sOne
    have h1 := F3_act s p0
    rw [hs, sOne_smul_p0, F3_p0, Eg_act, hs, sOne_det] at h1
    have hv1 : sOne.val.mulVec e1 = e1 := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [sOne_val0, sOne_val1]
      fin_cases i <;> simp [e1, e2]
    have hv2 : sOne.val.mulVec e2 = -e2 := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [sOne_val0, sOne_val1]
      fin_cases i <;> simp [e1, e2]
    rw [hv1, hv2, Eg_neg_right] at h1
    rw [F3_p0]
    have h2 : Eg e1 e2 = (((-1 : ℤ) : ℚ)) • F3 p0.swap := h1
    simp at h2
    rw [h2]; simp
  rw [h, map_neg, smul_neg]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
