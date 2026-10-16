module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Sign
public import TernaryPeriodPolynomials.Building.FreeResolution.Orientation
public import Mathlib.Algebra.BigOperators.Sym
public import Mathlib.LinearAlgebra.Matrix.Transvection

@[expose] public section


/-!
# Lemma B.1, boundary route: the augmentation of the oriented cell complex is `GL₃(ℤ)`-equivariant

The orientation `epsMod` of a vertex (determinant over `𝔽₃` of the rank-one rows of its six labels in label order)
transforms under `g ∈ GL₃(ℤ)` by the sign `cellSign g T` of the label reordering times the determinant of
`Sym² ḡ`, which is `det(ḡ)⁴ = 1` over `𝔽₃` (`det_symSq`, by the transvection/diagonal induction of Mathlib).
Hence `epsQ (g C) * cellSign g C = epsQ C` for the vertices `C` (`epsQ_equiv`), and the augmentation
of the library is a morphism of `GL₃(ℤ)`-representations.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPeriodPolynomials.FreeResolution GeneralEisenstein Matrix
  TernaryPeriodPolynomials.Argument.Lemma33.Retract

theorem det_symSq_tv01 {K : Type} [CommRing K] (c : K) :
    (symSq (Matrix.transvection (0 : Fin 3) 1 c)).det = 1 := by
  simp [symSq, Matrix.transvection, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
theorem det_symSq_tv02 {K : Type} [CommRing K] (c : K) :
    (symSq (Matrix.transvection (0 : Fin 3) 2 c)).det = 1 := by
  simp [symSq, Matrix.transvection, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
theorem det_symSq_tv10 {K : Type} [CommRing K] (c : K) :
    (symSq (Matrix.transvection (1 : Fin 3) 0 c)).det = 1 := by
  simp [symSq, Matrix.transvection, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
theorem det_symSq_tv12 {K : Type} [CommRing K] (c : K) :
    (symSq (Matrix.transvection (1 : Fin 3) 2 c)).det = 1 := by
  simp [symSq, Matrix.transvection, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
theorem det_symSq_tv20 {K : Type} [CommRing K] (c : K) :
    (symSq (Matrix.transvection (2 : Fin 3) 0 c)).det = 1 := by
  simp [symSq, Matrix.transvection, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
theorem det_symSq_tv21 {K : Type} [CommRing K] (c : K) :
    (symSq (Matrix.transvection (2 : Fin 3) 1 c)).det = 1 := by
  simp [symSq, Matrix.transvection, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_symSq_transvection {K : Type} [CommRing K] (i j : Fin 3) (hij : i ≠ j) (c : K) :
    (symSq (Matrix.transvection i j c)).det = 1 := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact det_symSq_tv01 c
  · exact det_symSq_tv02 c
  · exact det_symSq_tv10 c
  · exact absurd rfl hij
  · exact det_symSq_tv12 c
  · exact det_symSq_tv20 c
  · exact det_symSq_tv21 c
  · exact absurd rfl hij

theorem det_symSq_diagonal {K : Type} [CommRing K] (D : Fin 3 → K) :
    (symSq (Matrix.diagonal D)).det = (D 0 * D 1 * D 2) ^ 4 := by
  simp [symSq, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem det_symSq {K : Type} [Field K] (H : Matrix (Fin 3) (Fin 3) K) (hH : H.det ≠ 0) :
    (symSq H).det = H.det ^ 4 := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => (symSq M).det = M.det ^ 4) H hH ?_ ?_ ?_
  · intro D _
    rw [det_symSq_diagonal, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ, mul_assoc]
  · intro t
    have h := det_symSq_transvection t.i t.j t.hij t.c
    have e : t.toMatrix = Matrix.transvection t.i t.j t.c := rfl
    rw [e, h, det_transvection_of_ne _ _ t.hij]
    simp
  · intro A B _ _ hA hB
    rw [orient_symSq_mul, Matrix.det_mul, hA, hB, Matrix.det_mul, mul_pow]

/-- **Re-sorting a determinant of label-sorted rows.** -/
theorem labelDet_relabel {K : Type} [CommRing K] (r r' : ℕ → Fin 6 → K) (X X' : Finset ℕ)
    (hX : X.card = 6) (hX' : X'.card = 6) (ψ : ℕ → ℕ) (hψmem : ∀ x ∈ X, ψ x ∈ X')
    (hψinj : Set.InjOn ψ (X : Set ℕ)) (S : Matrix (Fin 6) (Fin 6) K)
    (hS : ∀ x ∈ X, r' (ψ x) = S *ᵥ r x) :
    labelDet r' X' =
      (((∏ j : Fin 6, ∏ i ∈ Finset.Iio j, (if ψ (X.orderEmbOfFin hX i) < ψ (X.orderEmbOfFin hX j)
          then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) : K) * S.det * labelDet r X := by
  set xs := X.orderEmbOfFin hX with hxs
  set xs' := X'.orderEmbOfFin hX' with hxs'
  have hrange : ∀ i, ∃ j, xs' j = ψ (xs i) := by
    intro i
    have h1 : ψ (xs i) ∈ X' := hψmem _ (Finset.orderEmbOfFin_mem X hX i)
    have : ψ (xs i) ∈ Set.range xs' := by
      rw [hxs', Finset.range_orderEmbOfFin]; exact h1
    exact this
  choose σ hσ using hrange
  have hσinj : Function.Injective σ := by
    intro i k h
    have h1 : ψ (xs i) = ψ (xs k) := by rw [← hσ i, ← hσ k, h]
    have h2 := hψinj (Finset.orderEmbOfFin_mem X hX i) (Finset.orderEmbOfFin_mem X hX k) h1
    exact xs.injective h2
  let σe : Equiv.Perm (Fin 6) := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσinj)
  have hσe : ∀ i, σe i = σ i := fun i => rfl
  set A : Matrix (Fin 6) (Fin 6) K := Matrix.of (sortedRows r X hX) with hA
  set B : Matrix (Fin 6) (Fin 6) K := Matrix.of (sortedRows r' X' hX') with hB
  have hmat : A * Sᵀ = B.submatrix σe id := by
    ext i k
    have h1 : B (σe i) k = r' (ψ (xs i)) k := by
      rw [hσe]
      simp only [hB, Matrix.of_apply, sortedRows]
      rw [← hxs', hσ i]
    simp only [Matrix.submatrix_apply, id_eq]
    rw [h1, hS _ (Finset.orderEmbOfFin_mem X hX i)]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hA, Matrix.of_apply, sortedRows, Matrix.mulVec,
      dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hdet : A.det * S.det = ((Equiv.Perm.sign σe : ℤˣ) : ℤ) * B.det := by
    have := congrArg Matrix.det hmat
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_permute] at this
    rw [this]
  have hsq : (((Equiv.Perm.sign σe : ℤˣ) : ℤ) : K) * (((Equiv.Perm.sign σe : ℤˣ) : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hsign : Equiv.Perm.sign σe = ∏ j : Fin 6, ∏ i ∈ Finset.Iio j,
      (if ψ (xs i) < ψ (xs j) then (1 : ℤˣ) else -1) := by
    rw [Equiv.Perm.sign_eq_prod_prod_Iio]
    refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i _ => ?_
    have : σe i < σe j ↔ ψ (xs i) < ψ (xs j) := by
      rw [hσe, hσe, ← hσ i, ← hσ j]
      exact xs'.lt_iff_lt.symm
    simp only [this]
  have e1 : labelDet r X = A.det := by rw [labelDet, dite_eq_left hX]
  have e2 : labelDet r' X' = B.det := by rw [labelDet, dite_eq_left hX']
  rw [e1, e2, ← hsign]
  have hd := hdet
  calc B.det = (((Equiv.Perm.sign σe : ℤˣ) : ℤ) : K) * ((((Equiv.Perm.sign σe : ℤˣ) : ℤ) : K) * B.det) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = _ := by rw [← hd]; ring


theorem prod_sym2_filter_not_isDiag' {ι M : Type} [LinearOrder ι] [CommMonoid M]
    (s : Finset ι) (p : Sym2 ι → M) :
    ∏ i ∈ s.sym2 with ¬ i.IsDiag, p i = ∏ i ∈ s.offDiag with i.1 < i.2, p s(i.1, i.2) := by
  rw [Finset.offDiag_filter_lt_eq_filter_le]
  conv_rhs => rw [← Finset.prod_subtype_eq_prod_filter]
  refine (Finset.prod_equiv Sym2.sortEquiv.symm ?_ ?_).symm
  all_goals aesop

theorem prod_Iio_eq_prod_lt {M : Type} [CommMonoid M] {n : ℕ} (f : Fin n → Fin n → M) :
    ∏ j : Fin n, ∏ i ∈ Finset.Iio j, f i j =
      ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)) with p.1 < p.2, f p.1 p.2 := by
  rw [Finset.prod_filter, Finset.univ_product_univ.symm, Finset.prod_product_right]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext i; simp

/-- The orientation sign as a product over the label-sorted pairs of a sorted enumeration of the lines. -/
theorem cellSign_eq_prod (g : IntegralGL3) (e : Fin 6 → Line) (he : Function.Injective e) :
    cellSign g (Finset.univ.image e) =
      ∏ j : Fin 6, ∏ i ∈ Finset.Iio j, pairSign g (e i) (e j) := by
  unfold cellSign
  rw [Finset.sym2_image, Finset.prod_image (fun z _ z' _ h => Sym2.map.injective he h)]
  rw [prod_Iio_eq_prod_lt (fun i j => pairSign g (e i) (e j))]
  have hdiag : ∀ z ∈ (Finset.univ : Finset (Fin 6)).sym2, z.IsDiag →
      Sym2.lift ⟨pairSign g, pairSign_comm g⟩ (Sym2.map e z) = 1 := by
    intro z _ hz
    induction z using Sym2.ind with
    | h a b =>
      have : a = b := by simpa using hz
      subst this
      simp [pairSign_self]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.sym2) (fun z => ¬ z.IsDiag)]
  have h2 : ∏ z ∈ (Finset.univ : Finset (Fin 6)).sym2 with ¬ ¬ z.IsDiag,
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


/-- The reduction modulo three of an integral matrix. -/
def gbar (g : IntegralGL3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  (g : Matrix (Fin 3) (Fin 3) ℤ).map (Int.cast : ℤ → ZMod 3)

theorem det_gbar_ne_zero (g : IntegralGL3) : (gbar g).det ≠ 0 := by
  have h1 : IsUnit (g : Matrix (Fin 3) (Fin 3) ℤ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have h2 : (gbar g).det = (Int.castRingHom (ZMod 3)) (g : Matrix (Fin 3) (Fin 3) ℤ).det := by
    rw [RingHom.map_det]
    rfl
  rw [h2]
  exact (h1.map (Int.castRingHom (ZMod 3))).ne_zero

theorem det_symSq_gbar (g : IntegralGL3) : (symSq (gbar g)).det = 1 := by
  rw [det_symSq _ (det_gbar_ne_zero g)]
  have h := ZMod.pow_card_sub_one_eq_one (det_gbar_ne_zero g)
  have h2 : (gbar g).det ^ 2 = 1 := h
  calc (gbar g).det ^ 4 = ((gbar g).det ^ 2) ^ 2 := by ring
    _ = 1 := by rw [h2]; norm_num

theorem labelRow_label_smul (g : IntegralGL3) (ℓ : Line) :
    labelRow (g • ℓ).label = symSq (gbar g) *ᵥ labelRow ℓ.label := by
  induction ℓ using Line.ind with
  | h x =>
    rw [smul_mk, Line.label_mk, Line.label_mk, labelRow_labelVec, labelRow_labelVec, red_mv,
      rankOne_mulVec]
    rfl

/-- **Transformation of the orientation of a vertex under `GL₃(ℤ)`.** -/
theorem epsMod_smul_gl (g : IntegralGL3) (T : Finset Line) (hT : T.card = 6)
    (hinj : Set.InjOn Line.label (T : Set Line))
    (hginj : Set.InjOn Line.label ((g • T : Finset Line) : Set Line)) :
    ∃ s : ℤˣ, epsMod (g • T) = (((s : ℤˣ) : ℤ) : ZMod 3) * epsMod T ∧
      cellSign g T = (((s : ℤˣ) : ℤ) : ℚ) := by
  set X : Finset ℕ := T.image Line.label with hXdef
  set X' : Finset ℕ := (g • T).image Line.label with hX'def
  have hX : X.card = 6 := by rw [hXdef, Finset.card_image_of_injOn hinj, hT]
  have hX' : X'.card = 6 := by rw [hX'def, Finset.card_image_of_injOn hginj, card_smul_gl, hT]
  set ψ : ℕ → ℕ := fun n => if h : ∃ t ∈ T, t.label = n then (g • h.choose).label else 0 with hψdef
  have hψ : ∀ t ∈ T, ψ t.label = (g • t).label := by
    intro t ht
    have h : ∃ t' ∈ T, t'.label = t.label := ⟨t, ht, rfl⟩
    rw [hψdef]
    simp only [dite_eq_left h]
    have := hinj h.choose_spec.1 ht h.choose_spec.2
    rw [this]
  have hmem : ∀ x ∈ X, ψ x ∈ X' := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    rw [hψ t ht]
    exact Finset.mem_image.mpr ⟨g • t, Finset.smul_mem_smul_finset ht, rfl⟩
  have hψinj : Set.InjOn ψ (X : Set ℕ) := by
    intro x hx y hy hxy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    rw [hψ t ht, hψ t' ht'] at hxy
    have h1 : g • t = g • t' :=
      hginj (Finset.mem_coe.mpr (Finset.smul_mem_smul_finset ht))
        (Finset.mem_coe.mpr (Finset.smul_mem_smul_finset ht')) hxy
    rw [MulAction.injective g h1]
  have hS : ∀ x ∈ X, labelRow (ψ x) = symSq (gbar g) *ᵥ labelRow x := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    rw [hψ t ht, labelRow_label_smul]
  have hrel := labelDet_relabel labelRow labelRow X X' hX hX' ψ hmem hψinj (symSq (gbar g)) hS
  set xs := X.orderEmbOfFin hX with hxs
  refine ⟨∏ j : Fin 6, ∏ i ∈ Finset.Iio j,
    (if ψ (xs i) < ψ (xs j) then (1 : ℤˣ) else -1), ?_, ?_⟩
  · unfold epsMod
    rw [← hX'def, ← hXdef, hrel, det_symSq_gbar, mul_one]
  · -- the enumeration of `T` in label order
    have hex : ∀ i : Fin 6, ∃ t ∈ T, t.label = xs i := by
      intro i
      exact Finset.mem_image.mp (Finset.orderEmbOfFin_mem X hX i)
    choose e he hel using hex
    have hlt : ∀ i j : Fin 6, i < j → (e i).label < (e j).label := by
      intro i j hij
      rw [hel, hel]
      exact xs.strictMono hij
    have heinj : Function.Injective e := by
      intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := hlt i j h
        rw [hij] at this
        exact lt_irrefl _ this
      · have := hlt j i h
        rw [hij] at this
        exact lt_irrefl _ this
    have hTe : T = Finset.univ.image e := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact he i
      · rw [hT, Finset.card_image_of_injective _ heinj]
        simp
    rw [hTe, cellSign_eq_prod g e heinj]
    rw [Units.coe_prod, Int.cast_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Units.coe_prod, Int.cast_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i < j := Finset.mem_Iio.mp hi
    have hl := hlt i j hij
    have hne : (e i).label ≠ (e j).label := hl.ne
    have hgne : (g • e i).label ≠ (g • e j).label := by
      intro h
      have h1 : g • e i = g • e j :=
        hginj (Finset.mem_coe.mpr (Finset.smul_mem_smul_finset (he i)))
          (Finset.mem_coe.mpr (Finset.smul_mem_smul_finset (he j))) h
      exact hne (by rw [MulAction.injective g h1])
    have hψi : ψ (xs i) = (g • e i).label := by rw [← hel i, hψ _ (he i)]
    have hψj : ψ (xs j) = (g • e j).label := by rw [← hel j, hψ _ (he j)]
    rw [hψi, hψj]
    unfold pairSign
    rw [ite_eq_left ⟨hne, hgne⟩]
    have h1 : lsgn (e i) (e j) = 1 := by unfold lsgn; rw [ite_eq_left hl]
    rw [h1, one_mul]
    unfold lsgn
    by_cases hlt' : (g • e i).label < (g • e j).label
    · rw [ite_eq_left hlt', ite_eq_left hlt']
      simp
    · have h2 : (g • e j).label < (g • e i).label := lt_of_le_of_ne (not_lt.mp hlt') (Ne.symm hgne)
      rw [ite_eq_right hlt', ite_eq_right hlt', ite_eq_left h2]
      simp

theorem iotaQ_neg (x : ZMod 3) : iotaQ (-x) = - iotaQ x := by
  revert x; decide

/-- **The augmentation sign of a vertex is `GL₃(ℤ)`-equivariant.** -/
theorem epsQ_equiv (g : IntegralGL3) (C : Cell) (hC : C.grade = 0) :
    epsQ (glCell g C) * cellSign g C.val = epsQ C := by
  have hcard : C.val.card = 6 := by
    have h1 := C.card_le_six
    unfold Cell.grade at hC
    omega
  have hcard' : (glCell g C).val.card = 6 := by rw [glCell_val, card_smul_gl, hcard]
  obtain ⟨s, hs, hsign⟩ := epsMod_smul_gl g C.val hcard C.isCell.2.label_injOn
    (by rw [← glCell_val]; exact (glCell g C).isCell.2.label_injOn)
  unfold epsQ
  rw [ite_eq_left hcard', ite_eq_left hcard, glCell_val, hs, hsign]
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp
  · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    rw [iotaQ_neg]
    ring

end TernaryPeriodPolynomials.Argument.AppendixBResidue
