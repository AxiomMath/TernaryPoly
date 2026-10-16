module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Tree

@[expose] public section


/-!
# Lemma B.1, boundary route: oriented cells as ordered tuples of lines

For an injective tuple `ℓ : Fin k → Line` whose set of lines is a cell of grade `6 - k`, `tupleVec n ℓ` is the
element `sgnLab ℓ • [cell]` of the oriented cell module: the class of the cell with the orientation of the ordered
tuple `ℓ` (`sgnLab ℓ = ± 1` compares the order of `ℓ` with the label order).  Then

* `tupleVec_twist`: `g • [ℓ] = [g ℓ]` for every `g ∈ GL₃(ℤ)` (no cocycle);
* `tupleVec_perm`: `[ℓ ∘ π] = sign π • [ℓ]`;
* `tupleVec_d`: `d [ℓ] = ∑_{w ∈ nbrs} [w, ℓ]`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Finsupp TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract

/-- The orientation sign of an ordered tuple of lines relative to the label order. -/
def sgnLab {k : ℕ} (ℓ : Fin k → Line) : ℚ := ∏ j : Fin k, ∏ i ∈ Finset.Iio j, lsgn (ℓ i) (ℓ j)

/-- The generalization of `cellSign_eq_prod` to tuples of any length. -/
theorem cellSign_eq_prod_tuple {n : ℕ} (g : IntegralGL3) (e : Fin n → Line) (he : Function.Injective e) :
    cellSign g (Finset.univ.image e) =
      ∏ j : Fin n, ∏ i ∈ Finset.Iio j, pairSign g (e i) (e j) := by
  unfold cellSign
  rw [Finset.sym2_image, Finset.prod_image (fun z _ z' _ h => Sym2.map.injective he h)]
  rw [prod_Iio_eq_prod_lt (fun i j => pairSign g (e i) (e j))]
  have hdiag : ∀ z ∈ (Finset.univ : Finset (Fin n)).sym2, z.IsDiag →
      Sym2.lift ⟨pairSign g, pairSign_comm g⟩ (Sym2.map e z) = 1 := by
    intro z _ hz
    induction z using Sym2.ind with
    | h a b =>
      have : a = b := by simpa using hz
      subst this
      simp [pairSign_self]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.sym2) (fun z => ¬ z.IsDiag)]
  have h2 : ∏ z ∈ (Finset.univ : Finset (Fin n)).sym2 with ¬ ¬ z.IsDiag,
      Sym2.lift ⟨pairSign g, pairSign_comm g⟩ (Sym2.map e z) = 1 := by
    refine Finset.prod_eq_one fun z hz => ?_
    rw [Finset.mem_filter] at hz
    exact hdiag z hz.1 (not_not.mp hz.2)
  rw [h2, mul_one, prod_sym2_filter_not_isDiag']
  simp only [Sym2.map_mk, Sym2.lift_mk]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, hlt⟩; exact hlt
  · intro hlt; exact ⟨hlt.ne, hlt⟩

theorem cellSign_tuple {k : ℕ} (g : IntegralGL3) (ℓ : Fin k → Line) (hinj : Function.Injective ℓ)
    (hl : Set.InjOn Line.label (Finset.univ.image ℓ : Finset Line))
    (hgl : Set.InjOn Line.label (Finset.univ.image fun i => g • ℓ i : Finset Line)) :
    cellSign g (Finset.univ.image ℓ) = sgnLab ℓ * sgnLab (fun i => g • ℓ i) := by
  rw [cellSign_eq_prod_tuple g ℓ hinj, sgnLab, sgnLab, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hij : i ≠ j := (Finset.mem_Iio.mp hi).ne
  have h1 : (ℓ i).label ≠ (ℓ j).label := fun e =>
    hij (hinj (hl (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))) e))
  have h2 : (g • ℓ i).label ≠ (g • ℓ j).label := fun e =>
    hij (hinj (MulAction.injective g (hgl (Finset.mem_coe.mpr
      (Finset.mem_image_of_mem (fun i => g • ℓ i) (Finset.mem_univ i)))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem (fun i => g • ℓ i) (Finset.mem_univ j))) e)))
  unfold pairSign
  rw [ite_eq_left ⟨h1, h2⟩]

/-- The tuple `ℓ` of `k` lines is an oriented cell of grade `n`. -/
def TupleOK (n : ℕ) {k : ℕ} (ℓ : Fin k → Line) : Prop :=
  Function.Injective ℓ ∧ IsCell (Finset.univ.image ℓ) ∧ 6 - k = n

theorem TupleOK.card {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK n ℓ) : (Finset.univ.image ℓ).card = k := by
  rw [Finset.card_image_of_injective _ h.1]; simp

/-- The cell of a tuple. -/
def tupleCell {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK n ℓ) : Graded n :=
  ⟨⟨Finset.univ.image ℓ, h.2.1⟩, by
    change 6 - (Finset.univ.image ℓ).card = n
    rw [h.card]; exact h.2.2⟩

/-- The class of the ordered cell `ℓ` in the oriented cell module (zero if `ℓ` is not an oriented cell). -/
def tupleVec (n : ℕ) {k : ℕ} (ℓ : Fin k → Line) : Graded n →₀ ℚ :=
  if h : TupleOK n ℓ then sgnLab ℓ • single (tupleCell h) 1 else 0

theorem tupleVec_of_ok {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK n ℓ) :
    tupleVec n ℓ = sgnLab ℓ • single (tupleCell h) 1 := by
  unfold tupleVec; rw [dite_eq_left h]

theorem TupleOK.smul {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK n ℓ) (g : IntegralGL3) :
    TupleOK n (fun i => g • ℓ i) := by
  refine ⟨fun i j e => h.1 (MulAction.injective g e), ?_, h.2.2⟩
  have : Finset.univ.image (fun i => g • ℓ i) = g • Finset.univ.image ℓ := by
    rw [Finset.smul_finset_def, Finset.image_image]; rfl
  rw [this]
  exact (isCell_smul_gl g _).mpr h.2.1

theorem tupleCell_smul {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK n ℓ) (g : IntegralGL3) :
    tupleCell (h.smul g) = glGraded n g (tupleCell h) := by
  apply Subtype.ext
  apply Cell.ext
  change Finset.univ.image (fun i => g • ℓ i) = g • Finset.univ.image ℓ
  rw [Finset.smul_finset_def, Finset.image_image]; rfl

/-- **Equivariance**: `g • [ℓ] = [g ℓ]`. -/
theorem tupleVec_twist {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK n ℓ) (g : IntegralGL3) :
    twistLin n g (tupleVec n ℓ) = tupleVec n (fun i => g • ℓ i) := by
  rw [tupleVec_of_ok h, tupleVec_of_ok (h.smul g), map_smul, twistLin_single, tupleCell_smul h g,
    Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  congr 1
  have hl : Set.InjOn Line.label (Finset.univ.image ℓ : Finset Line) :=
    (tupleCell h).1.isCell.2.label_injOn
  have hgl : Set.InjOn Line.label (Finset.univ.image fun i => g • ℓ i : Finset Line) :=
    (tupleCell (h.smul g)).1.isCell.2.label_injOn
  have e := cellSign_tuple g ℓ h.1 hl hgl
  have hsq : sgnLab ℓ * sgnLab ℓ = 1 := by
    unfold sgnLab
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => lsgn_mul_self _ _
  change sgnLab ℓ * cellSign g (tupleCell h).1.val = sgnLab (fun i => g • ℓ i)
  have : (tupleCell h).1.val = Finset.univ.image ℓ := rfl
  rw [this, e]
  calc sgnLab ℓ * (sgnLab ℓ * sgnLab fun i => g • ℓ i)
      = (sgnLab ℓ * sgnLab ℓ) * sgnLab fun i => g • ℓ i := by ring
    _ = _ := by rw [hsq, one_mul]

theorem lsgn_ne_label {u v : Line} (h : u.label ≠ v.label) : lsgn u v = -lsgn v u := by
  rw [lsgn_swap h]; ring

theorem sgnLab_sq {k : ℕ} (ℓ : Fin k → Line) : sgnLab ℓ * sgnLab ℓ = 1 := by
  unfold sgnLab
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => lsgn_mul_self _ _

theorem TupleOK.label_ne {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK n ℓ) {i j : Fin k} (hij : i ≠ j) :
    (ℓ i).label ≠ (ℓ j).label := by
  intro e
  exact hij (h.1 ((tupleCell h).1.isCell.2.label_injOn
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))) e))

theorem sgnLab_perm {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK n ℓ) (π : Equiv.Perm (Fin k)) :
    sgnLab (fun i => ℓ (π i)) = (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℚ) * sgnLab ℓ := by
  set f : Fin k → Fin k → ℚ := fun i j => if i = j then 0 else lsgn (ℓ i) (ℓ j) with hf
  have hanti : ∀ i j, f i j = -f j i := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [hf]
    · simp only [hf, ite_eq_right hij, ite_eq_right (Ne.symm hij)]
      exact lsgn_ne_label (h.label_ne hij)
  have key := Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod π hanti
  have e1 : sgnLab (fun i => ℓ (π i)) = ∏ j : Fin k, ∏ i ∈ Finset.Iio j, f (π i) (π j) := by
    unfold sgnLab
    refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i hi => ?_
    have : π i ≠ π j := fun e => (Finset.mem_Iio.mp hi).ne (π.injective e)
    simp [hf, this]
  have e2 : sgnLab ℓ = ∏ j : Fin k, ∏ i ∈ Finset.Iio j, f i j := by
    unfold sgnLab
    refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i hi => ?_
    have : i ≠ j := (Finset.mem_Iio.mp hi).ne
    simp [hf, this]
  rw [e1, e2, key]

theorem TupleOK.perm {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK n ℓ) (π : Equiv.Perm (Fin k)) :
    TupleOK n (fun i => ℓ (π i)) := by
  refine ⟨fun i j e => π.injective (h.1 e), ?_, h.2.2⟩
  have : Finset.univ.image (fun i => ℓ (π i)) = Finset.univ.image ℓ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨π i, hi⟩, fun ⟨i, hi⟩ => ⟨π.symm i, by simpa using hi⟩⟩
  rw [this]; exact h.2.1

/-- **Permuting the tuple multiplies the class by the sign.** -/
theorem tupleVec_perm {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK n ℓ) (π : Equiv.Perm (Fin k)) :
    tupleVec n (fun i => ℓ (π i)) = (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℚ) • tupleVec n ℓ := by
  have hc : tupleCell (h.perm π) = tupleCell h := by
    apply Subtype.ext; apply Cell.ext
    change Finset.univ.image (fun i => ℓ (π i)) = Finset.univ.image ℓ
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨π i, hi⟩, fun ⟨i, hi⟩ => ⟨π.symm i, by simpa using hi⟩⟩
  rw [tupleVec_of_ok h, tupleVec_of_ok (h.perm π), hc, sgnLab_perm h π, smul_smul]
theorem prod_Iio_succ {M : Type} [CommMonoid M] {k : ℕ} (j : Fin k) (F : Fin (k+1) → M) :
    ∏ i ∈ Finset.Iio j.succ, F i = F 0 * ∏ i ∈ Finset.Iio j, F i.succ := by
  have h1 : Finset.Iio j.succ = insert (0 : Fin (k+1)) ((Finset.Iio j).map (Fin.succEmb k)) := by
    ext x
    simp only [Finset.mem_Iio, Finset.mem_insert, Finset.mem_map]
    constructor
    · intro hx
      rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨y, rfl⟩
      · left; rfl
      · right; exact ⟨y, Fin.succ_lt_succ_iff.mp hx, rfl⟩
    · rintro (rfl | ⟨y, hy, rfl⟩)
      · exact Fin.succ_pos j
      · exact Fin.succ_lt_succ_iff.mpr hy
  rw [h1, Finset.prod_insert (by simp), Finset.prod_map]
  rfl


theorem sgnLab_cons {k : ℕ} (w : Line) (ℓ : Fin k → Line) :
    sgnLab (Fin.cons w ℓ : Fin (k + 1) → Line) = (∏ i, lsgn w (ℓ i)) * sgnLab ℓ := by
  unfold sgnLab
  rw [Fin.prod_univ_succ]
  have h0 : Finset.Iio (0 : Fin (k + 1)) = ∅ := by
    ext x; simp
  rw [h0, Finset.prod_empty, one_mul]
  have : ∀ j : Fin k, ∏ i ∈ Finset.Iio j.succ, lsgn ((Fin.cons w ℓ : Fin (k + 1) → Line) i)
      ((Fin.cons w ℓ : Fin (k + 1) → Line) j.succ) = lsgn w (ℓ j) * ∏ i ∈ Finset.Iio j, lsgn (ℓ i) (ℓ j) := by
    intro j
    rw [prod_Iio_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  simp only [this, Finset.prod_mul_distrib]

theorem insSignQ_tuple {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK n ℓ) {w : Line} (hw : w ∈ nbrs (Finset.univ.image ℓ)) :
    insSignQ (Finset.univ.image ℓ) w = ∏ i, lsgn w (ℓ i) := by
  have hcell := (mem_nbrs' hw)
  have hinj : Set.InjOn Line.label ((Finset.univ.image ℓ : Finset Line) : Set Line) :=
    (tupleCell h).1.isCell.2.label_injOn
  have hne : ∀ t ∈ Finset.univ.image ℓ, t.label ≠ w.label := by
    intro t ht e
    have hs : IsSimplex (insert w (Finset.univ.image ℓ)) := hcell.2.2
    have := hs.label_injOn (Finset.mem_coe.mpr (Finset.mem_insert_of_mem ht))
      (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) e
    exact hcell.2.1 (this ▸ ht)
  have hR : ∏ i, lsgn w (ℓ i) = (-1) ^ k * ∏ i, lsgn (ℓ i) w := by
    rw [Finset.prod_congr rfl (fun i _ =>
      lsgn_ne_label (Ne.symm (hne _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))), Finset.prod_neg]
    simp
  rw [hR, insSignQ_eq _ _ hinj hne, h.card, Finset.prod_image (fun a _ b _ e => h.1 e)]

theorem image_cons {k : ℕ} (w : Line) (ℓ : Fin k → Line) :
    Finset.univ.image (Fin.cons w ℓ : Fin (k + 1) → Line) = insert w (Finset.univ.image ℓ) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · left; rfl
    · right; exact ⟨j, by simp⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨i.succ, by simp⟩

theorem TupleOK.cons {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK (n + 1) ℓ) {w : Line}
    (hw : w ∈ nbrs (Finset.univ.image ℓ)) : TupleOK n (Fin.cons w ℓ : Fin (k + 1) → Line) := by
  have hcell := mem_nbrs' hw
  refine ⟨?_, ?_, ?_⟩
  · rw [Fin.cons_injective_iff]
    refine ⟨?_, h.1⟩
    rintro ⟨i, hi⟩
    exact hcell.2.1 (hi ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · rw [image_cons]
    exact ⟨hcell.1.mono (Finset.subset_insert _ _), hcell.2.2⟩
  · have := h.2.2
    omega

theorem tupleCell_cons_val {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK (n + 1) ℓ) {w : Line}
    (hw : w ∈ nbrs (Finset.univ.image ℓ)) :
    (tupleCell (h.cons hw)).1.val = insert w (Finset.univ.image ℓ) := by
  change Finset.univ.image (Fin.cons w ℓ : Fin (k + 1) → Line) = _
  exact image_cons w ℓ

/-- **The boundary of an ordered cell**: `d [ℓ] = ∑_{w ∈ nbrs} [w, ℓ]`. -/
theorem tupleVec_d {n k : ℕ} {ℓ : Fin k → Line} (h : TupleOK (n + 1) ℓ) :
    dLin n (tupleVec (n + 1) ℓ) =
      ∑ w ∈ nbrs (Finset.univ.image ℓ), tupleVec n (Fin.cons w ℓ : Fin (k + 1) → Line) := by
  rw [tupleVec_of_ok h, map_smul, dLin_single, one_smul]
  ext D
  rw [Finsupp.smul_apply, Finsupp.finsetSum_apply, dGr_apply, incQ_apply]
  have hcob := coboundaryOfQ_apply (tupleCell h).1.val D.1.val
  unfold coboundaryOfQ at hcob ⊢
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  change sgnLab ℓ * ∑ w ∈ nbrs (Finset.univ.image ℓ), (if insert w (Finset.univ.image ℓ) = D.1.val
      then insSignQ (Finset.univ.image ℓ) w else 0) = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [tupleVec_of_ok (h.cons hw)]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have hD : tupleCell (h.cons hw) = D ↔ insert w (Finset.univ.image ℓ) = D.1.val := by
    constructor
    · intro e; rw [← e]; exact (tupleCell_cons_val h hw).symm
    · intro e; apply Subtype.ext; apply Cell.ext; rw [tupleCell_cons_val h hw]; exact e
  by_cases hDw : insert w (Finset.univ.image ℓ) = D.1.val
  · rw [ite_eq_left hDw, ite_eq_left (hD.mpr hDw), sgnLab_cons, insSignQ_tuple h hw]
    ring
  · rw [ite_eq_right hDw, ite_eq_right (fun e => hDw (hD.mp e))]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
