module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.GL

@[expose] public section


/-!
# Lemma B.1, boundary route: the orientation cocycle of the oriented cell model

`cellSign g T ∈ {±1}` is the sign of the permutation that the line map `g` induces on the label-ordered lines of
the cell `T` (the parity of the number of label inversions).  It satisfies the cocycle identity
`cellSign (g h) T = cellSign h T * cellSign g (h T)` on label-injective sets, is `1` for label-preserving `g`, and
is compatible with the boundary signs: `insSign` of the library satisfies
`insSignQ T w * cellSign g (T ∪ {w}) = cellSign g T * insSignQ (g T) (g w)` (`insSignQ_cellSign`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPeriodPolynomials.FreeResolution TernaryPeriodPolynomials.TopVanishing
  GeneralEisenstein TernaryPeriodPolynomials.Argument.Lemma33.Retract

/-- The sign comparing two labels. -/
def lsgn (u v : Line) : ℚ := if u.label < v.label then 1 else if v.label < u.label then -1 else 1

theorem lsgn_mul_self (u v : Line) : lsgn u v * lsgn u v = 1 := by
  unfold lsgn
  split_ifs <;> norm_num

theorem lsgn_swap {u v : Line} (h : u.label ≠ v.label) : lsgn v u = - lsgn u v := by
  unfold lsgn
  rcases lt_or_gt_of_ne h with h1 | h1
  · have h2 : ¬ v.label < u.label := not_lt.mpr h1.le
    simp [h1, h2]
  · have h2 : ¬ u.label < v.label := not_lt.mpr h1.le
    simp [h1, h2]

/-- The sign contributed by a pair of lines. -/
def pairSign (g : IntegralGL3) (a b : Line) : ℚ :=
  if a.label ≠ b.label ∧ (g • a).label ≠ (g • b).label then lsgn a b * lsgn (g • a) (g • b) else 1

theorem pairSign_comm (g : IntegralGL3) (a b : Line) : pairSign g a b = pairSign g b a := by
  unfold pairSign
  by_cases h : a.label ≠ b.label ∧ (g • a).label ≠ (g • b).label
  · rw [ite_eq_left h, ite_eq_left ⟨h.1.symm, h.2.symm⟩, lsgn_swap h.1, lsgn_swap h.2]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]

theorem pairSign_sq (g : IntegralGL3) (a b : Line) : pairSign g a b * pairSign g a b = 1 := by
  unfold pairSign
  split_ifs
  · have := lsgn_mul_self a b
    have := lsgn_mul_self (g • a) (g • b)
    nlinarith
  · norm_num

theorem pairSign_self (g : IntegralGL3) (a : Line) : pairSign g a a = 1 := by
  unfold pairSign
  simp

/-- The orientation sign of `g` on the set of lines `T`. -/
def cellSign (g : IntegralGL3) (T : Finset Line) : ℚ :=
  ∏ z ∈ T.sym2, Sym2.lift ⟨pairSign g, pairSign_comm g⟩ z

theorem cellSign_cons (g : IntegralGL3) (T : Finset Line) (w : Line) (hw : w ∉ T) :
    cellSign g (insert w T) = cellSign g T * ∏ t ∈ T, pairSign g w t := by
  rw [← Finset.cons_eq_insert w T hw]
  unfold cellSign
  rw [Finset.sym2_cons, Finset.prod_disjUnion, Finset.prod_map, Finset.prod_cons, mul_comm]
  change (∏ x ∈ T.sym2, Sym2.lift ⟨pairSign g, pairSign_comm g⟩ x) *
    (pairSign g w w * ∏ x ∈ T, pairSign g w x) = _
  rw [pairSign_self, one_mul]

theorem cellSign_of_label (g : IntegralGL3) (hg : ∀ a : Line, (g • a).label = a.label) (T : Finset Line) :
    cellSign g T = 1 := by
  unfold cellSign
  refine Finset.prod_eq_one fun z _ => ?_
  induction z using Sym2.ind with
  | h a b =>
    have e : lsgn (g • a) (g • b) = lsgn a b := by unfold lsgn; rw [hg, hg]
    simp only [Sym2.lift_mk, pairSign, e]
    split_ifs
    · exact lsgn_mul_self a b
    · rfl

theorem cellSign_one (T : Finset Line) : cellSign 1 T = 1 :=
  cellSign_of_label 1 (fun a => by rw [one_smul]) T

theorem pairSign_mul (g h : IntegralGL3) {T : Finset Line} (hT : Set.InjOn Line.label (T : Set Line))
    (hhT : Set.InjOn Line.label ((h • T : Finset Line) : Set Line))
    (hghT : Set.InjOn Line.label (((g * h) • T : Finset Line) : Set Line)) {a b : Line}
    (ha : a ∈ T) (hb : b ∈ T) :
    pairSign (g * h) a b = pairSign h a b * pairSign g (h • a) (h • b) := by
  by_cases hab : a = b
  · subst hab
    simp [pairSign_self]
  · have h1 : a.label ≠ b.label := fun e => hab (hT ha hb e)
    have hha : h • a ∈ h • T := Finset.smul_mem_smul_finset ha
    have hhb : h • b ∈ h • T := Finset.smul_mem_smul_finset hb
    have h2 : (h • a).label ≠ (h • b).label := fun e =>
      hab (MulAction.injective h (hhT hha hhb e))
    have hgha : (g * h) • a ∈ (g * h) • T := Finset.smul_mem_smul_finset ha
    have hghb : (g * h) • b ∈ (g * h) • T := Finset.smul_mem_smul_finset hb
    have h3 : ((g * h) • a).label ≠ ((g * h) • b).label := fun e =>
      hab (MulAction.injective (g * h) (hghT hgha hghb e))
    have h4 : (g • h • a).label ≠ (g • h • b).label := by
      rw [← mul_smul, ← mul_smul]; exact h3
    unfold pairSign
    rw [ite_eq_left ⟨h1, h3⟩, ite_eq_left ⟨h1, h2⟩, ite_eq_left ⟨h2, h4⟩, mul_smul, mul_smul]
    have := lsgn_mul_self (h • a) (h • b)
    calc lsgn a b * lsgn (g • h • a) (g • h • b)
        = lsgn a b * lsgn (g • h • a) (g • h • b) * (lsgn (h • a) (h • b) * lsgn (h • a) (h • b)) := by
          rw [this, mul_one]
      _ = _ := by ring

/-- **The cocycle identity.** -/
theorem cellSign_mul (g h : IntegralGL3) {T : Finset Line} (hT : Set.InjOn Line.label (T : Set Line))
    (hhT : Set.InjOn Line.label ((h • T : Finset Line) : Set Line))
    (hghT : Set.InjOn Line.label (((g * h) • T : Finset Line) : Set Line)) :
    cellSign (g * h) T = cellSign g (h • T) * cellSign h T := by
  have himg : cellSign g (h • T) =
      ∏ z ∈ T.sym2, Sym2.lift ⟨pairSign g, pairSign_comm g⟩ (Sym2.map (h • ·) z) := by
    unfold cellSign
    rw [Finset.smul_finset_def, Finset.sym2_image, Finset.prod_image]
    intro z _ z' _ hzz
    exact Sym2.map.injective (MulAction.injective h) hzz
  rw [himg, mul_comm, cellSign, cellSign, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun z hz => ?_
  induction z using Sym2.ind with
  | h a b =>
    have ha : a ∈ T := (Finset.mk_mem_sym2_iff.mp hz).1
    have hb : b ∈ T := (Finset.mk_mem_sym2_iff.mp hz).2
    simp only [Sym2.map_mk, Sym2.lift_mk]
    exact pairSign_mul g h hT hhT hghT ha hb

theorem prod_lsgn (T : Finset Line) (w : Line) (hT : ∀ t ∈ T, t.label ≠ w.label) :
    ∏ t ∈ T, lsgn t w = (-1) ^ (T.filter (fun t => w.label < t.label)).card := by
  have h : ∀ t ∈ T, lsgn t w = if w.label < t.label then (-1 : ℚ) else 1 := by
    intro t ht
    have hne := hT t ht
    unfold lsgn
    by_cases h1 : t.label < w.label
    · have h2 : ¬ w.label < t.label := not_lt.mpr h1.le
      simp [h1, h2]
    · have h2 : w.label < t.label := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm hne)
      simp [h1, h2]
  rw [Finset.prod_congr rfl h, Finset.prod_ite]
  simp

theorem insSignQ_eq (T : Finset Line) (w : Line) (hinj : Set.InjOn Line.label (T : Set Line))
    (hw : ∀ t ∈ T, t.label ≠ w.label) :
    insSignQ T w = (-1) ^ T.card * ∏ t ∈ T, lsgn t w := by
  rw [prod_lsgn T w hw, insSignQ, Finset.filter_image, Finset.card_image_of_injOn
    (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))]
  have hsum := Finset.card_filter_add_card_filter_not (s := T) (fun t : Line => t.label < w.label)
  have hcomp : T.filter (fun t => ¬ t.label < w.label) = T.filter (fun t => w.label < t.label) := by
    apply Finset.filter_congr
    intro t ht
    have := hw t ht
    constructor
    · intro h; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm this)
    · intro h; exact not_lt.mpr h.le
  rw [hcomp] at hsum
  rw [← hsum, pow_add]
  have : ((-1 : ℚ) ^ (T.filter (fun t => w.label < t.label)).card) *
      ((-1 : ℚ) ^ (T.filter (fun t => w.label < t.label)).card) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc (-1 : ℚ) ^ (T.filter (fun t => t.label < w.label)).card
      = (-1) ^ (T.filter (fun t => t.label < w.label)).card *
        ((-1) ^ (T.filter (fun t => w.label < t.label)).card *
          (-1) ^ (T.filter (fun t => w.label < t.label)).card) := by rw [this, mul_one]
    _ = _ := by ring

/-- **Compatibility of the orientation cocycle with the boundary signs.** -/
theorem insSignQ_cellSign (g : IntegralGL3) (T : Finset Line) (w : Line) (hw : w ∉ T)
    (hinj : Set.InjOn Line.label ((insert w T : Finset Line) : Set Line))
    (hginj : Set.InjOn Line.label ((g • insert w T : Finset Line) : Set Line)) :
    insSignQ T w * cellSign g (insert w T) = cellSign g T * insSignQ (g • T) (g • w) := by
  have hT : Set.InjOn Line.label (T : Set Line) :=
    hinj.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
  have hne : ∀ t ∈ T, t.label ≠ w.label := fun t ht e =>
    hw ((hinj (Finset.mem_insert_of_mem ht) (Finset.mem_insert_self _ _) e) ▸ ht)
  have hgT : Set.InjOn Line.label ((g • T : Finset Line) : Set Line) := by
    refine hginj.mono ?_
    rw [Finset.smul_finset_insert]
    intro x hx; exact Finset.mem_insert_of_mem hx
  have hgne : ∀ t ∈ T, (g • t).label ≠ (g • w).label := by
    intro t ht e
    have hmem1 : g • t ∈ g • insert w T :=
      Finset.smul_mem_smul_finset (Finset.mem_insert_of_mem ht)
    have hmem2 : g • w ∈ g • insert w T := Finset.smul_mem_smul_finset (Finset.mem_insert_self _ _)
    have := MulAction.injective g (hginj hmem1 hmem2 e)
    exact hw (this ▸ ht)
  have hgne' : ∀ t' ∈ g • T, t'.label ≠ (g • w).label := by
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_smul_finset.mp ht'
    exact hgne t ht
  rw [insSignQ_eq T w hT hne, insSignQ_eq (g • T) (g • w) hgT hgne', cellSign_cons g T w hw,
    card_smul_gl, Finset.smul_finset_def, Finset.prod_image (fun a _ b _ h => MulAction.injective g h)]
  have hpair : ∀ t ∈ T, pairSign g w t = lsgn t w * lsgn (g • t) (g • w) := by
    intro t ht
    have h1 : w.label ≠ t.label := fun e => hne t ht e.symm
    have h2 : (g • w).label ≠ (g • t).label := fun e => hgne t ht e.symm
    unfold pairSign
    rw [ite_eq_left ⟨h1, h2⟩, lsgn_swap h1.symm, lsgn_swap h2.symm]
    ring
  rw [Finset.prod_congr rfl hpair, Finset.prod_mul_distrib]
  have hsq : (∏ t ∈ T, lsgn t w) * (∏ t ∈ T, lsgn t w) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun t _ => lsgn_mul_self t w
  calc (-1) ^ T.card * (∏ t ∈ T, lsgn t w) *
        (cellSign g T * ((∏ t ∈ T, lsgn t w) * ∏ t ∈ T, lsgn (g • t) (g • w)))
      = (-1) ^ T.card * ((∏ t ∈ T, lsgn t w) * (∏ t ∈ T, lsgn t w)) * cellSign g T *
        ∏ t ∈ T, lsgn (g • t) (g • w) := by ring
    _ = _ := by rw [hsq]; ring

end TernaryPeriodPolynomials.Argument.AppendixBResidue
