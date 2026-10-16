module

public import TernaryPeriodPolynomials.Building.FreeResolution.Vertices
public import TernaryPeriodPolynomials.Building.FreeResolution.Sorting
public import TernaryPeriodPolynomials.Building.FreeResolution.Signs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.LinearCombination

@[expose] public section


/-!
# The orientation of a vertex modulo three

Original work by Claude Sonnet 5.5.

The orientation `epsMod T` of a set of lines is the determinant over `𝔽₃` of the rank-one rows of
the labels of `T`, listed in increasing label order. For a vertex `v` the six rows are the image of
the six rank-one rows of `A₀` under the invertible matrix `symSq F`, `F` the reduction of the
inverse frame of `v`; they span `𝔽₃⁶`, so `epsMod v.M ≠ 0`. Across an edge, the new row of the
neighbour is the negative of the old one modulo the other five rows, and the Laplace expansion
along the inserted row (`labelDet_insert`) shows that the orientations of the two endpoints cancel
against the insertion signs `insSign`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

open GeneralEisenstein Matrix

/-- The orientation modulo three of a set of lines: the determinant of the rank-one rows of its
labels in increasing label order. -/
def epsMod (T : Finset Line) : ZMod 3 := labelDet labelRow (T.image Line.label)

/-- `0, 1, -1 ∈ ℤ/3` as complex numbers. -/
def iota (x : ZMod 3) : ℂ := if x = 1 then 1 else if x = -1 then -1 else 0

/-! ### The embedding `iota` -/

theorem orient_zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = -1 := by
  revert x
  decide

theorem iota_zero : iota 0 = 0 := by
  have h1 : (0 : ZMod 3) ≠ 1 := by decide
  have h2 : (0 : ZMod 3) ≠ -1 := by decide
  unfold iota
  rw [ite_eq_right h1, ite_eq_right h2]

theorem iota_one : iota 1 = 1 := by
  unfold iota
  rw [ite_eq_left rfl]

theorem iota_neg_one : iota (-1) = -1 := by
  have h1 : (-1 : ZMod 3) ≠ 1 := by decide
  unfold iota
  rw [ite_eq_right h1, ite_eq_left rfl]

/-- `iota` is multiplicative. -/
theorem iota_mul (x y : ZMod 3) : iota (x * y) = iota x * iota y := by
  rcases orient_zmod3_cases x with rfl | rfl | rfl <;>
    rcases orient_zmod3_cases y with rfl | rfl | rfl
  · simp [iota_zero]
  · simp [iota_zero]
  · simp [iota_zero]
  · simp [iota_zero]
  · simp [iota_one]
  · simp [iota_one, iota_neg_one]
  · simp [iota_zero]
  · simp [iota_one]
  · simp [iota_one, iota_neg_one]

/-- `iota` is odd. -/
theorem iota_neg (x : ZMod 3) : iota (-x) = -iota x := by
  rcases orient_zmod3_cases x with rfl | rfl | rfl
  · rw [neg_zero, iota_zero, neg_zero]
  · rw [iota_neg_one, iota_one]
  · rw [neg_neg, iota_one, iota_neg_one, neg_neg]

/-- `iota` fixes the powers of `-1`. -/
theorem iota_neg_one_pow (n : ℕ) : iota ((-1) ^ n) = (-1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, iota_one]
  | succ n ih => rw [pow_succ, pow_succ, iota_mul, ih, iota_neg_one]

theorem orient_iota_ne_zero {x : ZMod 3} (hx : x ≠ 0) : iota x ≠ 0 := by
  rcases orient_zmod3_cases x with rfl | rfl | rfl
  · exact absurd rfl hx
  · rw [iota_one]
    exact one_ne_zero
  · rw [iota_neg_one]
    exact neg_ne_zero.mpr one_ne_zero

/-! ### The square-power map `symSq` is multiplicative -/

theorem orient_symSq_mul {K : Type} [CommRing K] (H H' : Matrix (Fin 3) (Fin 3) K) :
    symSq (H * H') = symSq H * symSq H' := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [symSq, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem orient_symSq_one {K : Type} [CommRing K] : symSq (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [symSq]

theorem orient_map_cast_mul (A B : Matrix (Fin 3) (Fin 3) ℤ) :
    (A * B).map (Int.cast : ℤ → ZMod 3) =
      A.map (Int.cast : ℤ → ZMod 3) * B.map (Int.cast : ℤ → ZMod 3) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.map_apply]

/-- The reduction modulo three of the inverse frame of a vertex. -/
def invFrameMod (v : Vtx) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ((v.frame⁻¹ : IntegralGL3) : Matrix (Fin 3) (Fin 3) ℤ).map (Int.cast : ℤ → ZMod 3)

/-- The reduction modulo three of the frame of a vertex. -/
def frameMod (v : Vtx) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ((v.frame : IntegralGL3) : Matrix (Fin 3) (Fin 3) ℤ).map (Int.cast : ℤ → ZMod 3)

theorem orient_invFrameMod_mul_frameMod (v : Vtx) : invFrameMod v * frameMod v = 1 := by
  have h : ((v.frame⁻¹ : IntegralGL3) : Matrix (Fin 3) (Fin 3) ℤ) *
      ((v.frame : IntegralGL3) : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  unfold invFrameMod frameMod
  rw [← orient_map_cast_mul, h]
  exact Matrix.map_one _ Int.cast_zero Int.cast_one

theorem orient_symSq_invFrameMod_mul (v : Vtx) :
    symSq (invFrameMod v) * symSq (frameMod v) = 1 := by
  rw [← orient_symSq_mul, orient_invFrameMod_mul_frameMod, orient_symSq_one]

/-! ### The rows of a vertex -/

theorem orient_labelRow_smul_mk (v : Vtx) (x : Vec) :
    labelRow (v.frame⁻¹ • Line.mk x).label = symSq (invFrameMod v) *ᵥ rankOne (red x) := by
  have h := rankOne_mulVec (invFrameMod v) (red x)
  rw [smul_mk, Line.label_mk, labelRow_labelVec, red_mv]
  exact h

theorem orient_rankOne_red (x : Vec) : rankOne (red x) = fun a => ((rankOne x a : ℤ) : ZMod 3) := by
  funext a
  fin_cases a <;> simp [rankOne, red]

/-- The rank-one relation of `A₀`, reduced modulo three. -/
theorem orient_rankOne_relation_mod (i : Fin 6) :
    rankOne (red (mNew i)) + rankOne (red (m i)) =
      ∑ k, ((relCoef i k : ℤ) : ZMod 3) • rankOne (red (m k)) := by
  funext a
  have h := congrArg (Int.cast : ℤ → ZMod 3) (congrFun (rankOne_relation i) a)
  simpa [orient_rankOne_red, Finset.sum_apply] using h

theorem orient_range_sortedRows {β : Type} {n k : ℕ} (r : ℕ → Fin n → β) (X : Finset ℕ)
    (h : X.card = k) : Set.range (sortedRows r X h) = r '' (X : Set ℕ) := by
  have e : sortedRows r X h = r ∘ (X.orderEmbOfFin h) := rfl
  rw [e, Set.range_comp, Finset.range_orderEmbOfFin]

theorem orient_top_le_span_rows (v : Vtx) :
    ⊤ ≤ Submodule.span (ZMod 3)
      (Set.range fun i : Fin 6 => labelRow (v.frame⁻¹ • Line.mk (m i)).label) := by
  intro y _
  have hz : symSq (frameMod v) *ᵥ y ∈ Submodule.span (ZMod 3)
      (Set.range fun k : Fin 6 => rankOne (red (m k))) := by
    rw [span_rankOne_m]
    trivial
  have hfun : (fun i : Fin 6 => labelRow (v.frame⁻¹ • Line.mk (m i)).label) =
      (Matrix.mulVecLin (symSq (invFrameMod v))) ∘ (fun k : Fin 6 => rankOne (red (m k))) := by
    funext i
    exact orient_labelRow_smul_mk v (m i)
  rw [hfun, Set.range_comp, Submodule.span_image]
  refine Submodule.mem_map.mpr ⟨symSq (frameMod v) *ᵥ y, hz, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, orient_symSq_invFrameMod_mul, Matrix.one_mulVec]

/-- The orientation of a vertex does not vanish. -/
theorem epsMod_ne_zero (v : Vtx) : epsMod v.M ≠ 0 := by
  have hX : (v.M.image Line.label).card = 6 := by
    rw [Finset.card_image_of_injOn v.label_injOn, v.card_M]
  unfold epsMod labelDet
  rw [dite_eq_left hX, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_rows_iff_isUnit]
  show LinearIndependent (ZMod 3) (sortedRows labelRow (v.M.image Line.label) hX)
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
  rw [orient_range_sortedRows]
  refine le_trans (orient_top_le_span_rows v) (Submodule.span_mono ?_)
  rintro _ ⟨i, rfl⟩
  exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (v.mem_M_of_index i)), rfl⟩

theorem iota_epsMod_ne_zero (v : Vtx) : iota (epsMod v.M) ≠ 0 :=
  orient_iota_ne_zero (epsMod_ne_zero v)

/-! ### Edges -/

theorem nb_M_eq (v : Vtx) {ℓ ℓ' : Line} (hℓ : ℓ ∈ v.M) (hℓ' : ℓ' ∈ (v.nb ℓ).M)
    (hℓ'v : ℓ' ∉ v.M) : (v.nb ℓ).M = insert ℓ' (v.M.erase ℓ) := by
  have hnot : ℓ' ∉ v.M.erase ℓ := fun h => hℓ'v (Finset.mem_of_mem_erase h)
  have hsub : insert ℓ' (v.M.erase ℓ) ⊆ (v.nb ℓ).M := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hℓ'
    · exact v.mem_nb_of_mem hℓ (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)
  have hcard : (v.nb ℓ).M.card ≤ (insert ℓ' (v.M.erase ℓ)).card := by
    have h1 := Finset.card_insert_of_notMem hnot
    have h2 := Finset.card_erase_of_mem hℓ
    have h3 := v.card_M
    have h4 := (v.nb ℓ).card_M
    omega
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

theorem orient_card_image_erase_label (v : Vtx) {ℓ : Line} (hℓ : ℓ ∈ v.M) :
    ((v.M.erase ℓ).image Line.label).card = 5 := by
  have h1 := Finset.card_image_of_injOn
    (v.label_injOn.mono (Finset.coe_subset.mpr (Finset.erase_subset ℓ v.M)))
  have h2 := Finset.card_erase_of_mem hℓ
  have h3 := v.card_M
  omega

theorem orient_label_notMem_image_erase (v : Vtx) {ℓ : Line} (hℓ : ℓ ∈ v.M) :
    ℓ.label ∉ (v.M.erase ℓ).image Line.label := by
  intro h
  obtain ⟨k, hk, hkl⟩ := Finset.mem_image.mp h
  exact Finset.ne_of_mem_erase hk (v.label_injOn (Finset.mem_of_mem_erase hk) hℓ hkl)

theorem orient_label_notMem_image_erase_nb (v : Vtx) {ℓ ℓ' : Line} (hℓ : ℓ ∈ v.M)
    (hℓ' : ℓ' ∈ (v.nb ℓ).M) (hℓ'v : ℓ' ∉ v.M) :
    ℓ'.label ∉ (v.M.erase ℓ).image Line.label := by
  intro h
  obtain ⟨k, hk, hkl⟩ := Finset.mem_image.mp h
  have hk' : k ∈ (v.nb ℓ).M :=
    v.mem_nb_of_mem hℓ (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)
  have hkℓ' := (v.nb ℓ).label_injOn hk' hℓ' hkl
  subst hkℓ'
  exact hℓ'v (Finset.mem_of_mem_erase hk)

/-- Across an edge, the rows of the two new lines add up to a combination of the common rows. -/
theorem orient_add_mem_span_rows (v : Vtx) {ℓ ℓ' : Line} (hℓ : ℓ ∈ v.M) (hℓ' : ℓ' ∈ (v.nb ℓ).M)
    (hℓ'v : ℓ' ∉ v.M) :
    labelRow ℓ'.label + labelRow ℓ.label ∈ Submodule.span (ZMod 3)
      (labelRow '' (((v.M.erase ℓ).image Line.label : Finset ℕ) : Set ℕ)) := by
  have hnb := nb_M_eq v hℓ hℓ' hℓ'v
  obtain ⟨i, rfl⟩ := v.exists_index hℓ
  have hℓ'eq : ℓ' = v.frame⁻¹ • Line.mk (mNew i) := by
    have hmem := v.mem_nb i
    rw [hnb] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h.symm
    · exact absurd (Finset.mem_of_mem_erase h) (v.new_not_mem i)
  rw [hℓ'eq, orient_labelRow_smul_mk, orient_labelRow_smul_mk, ← Matrix.mulVec_add,
    orient_rankOne_relation_mod, Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [Matrix.mulVec_smul]
  by_cases hk : k = i
  · subst hk
    rw [relCoef_self]
    simp
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    have hne : v.frame⁻¹ • Line.mk (m k) ≠ v.frame⁻¹ • Line.mk (m i) :=
      fun h => hk (mk_m_injective (MulAction.injective _ h))
    exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _
      (Finset.mem_erase.mpr ⟨hne, v.mem_M_of_index k⟩)), orient_labelRow_smul_mk v (m k)⟩

theorem orient_hsq_neg_one (n : ℕ) : (-1 : ZMod 3) ^ n * (-1) ^ n = 1 := by
  rw [← mul_pow, neg_mul_neg, one_mul, one_pow]

theorem orient_sign_cancel (a b D : ZMod 3) (p p' : ℕ) (ha : a = (-1) ^ p * D)
    (hb : b = (-1) ^ p' * (-D)) :
    iota a * (-1 : ℂ) ^ p + iota b * (-1 : ℂ) ^ p' = 0 := by
  have h1 : a * (-1) ^ p = D := by
    rw [ha]
    linear_combination D * orient_hsq_neg_one p
  have h2 : b * (-1) ^ p' = -D := by
    rw [hb]
    linear_combination (-D) * orient_hsq_neg_one p'
  have h3 : iota a * (-1 : ℂ) ^ p = iota D := by
    rw [← iota_neg_one_pow p, ← iota_mul, h1]
  have h4 : iota b * (-1 : ℂ) ^ p' = -iota D := by
    rw [← iota_neg_one_pow p', ← iota_mul, h2, iota_neg]
  rw [h3, h4, add_neg_cancel]

/-- The orientations of the two vertices of an edge cancel against the insertion signs. -/
theorem edge_sign (v : Vtx) {ℓ ℓ' : Line} (hℓ : ℓ ∈ v.M) (hℓ' : ℓ' ∈ (v.nb ℓ).M)
    (hℓ'v : ℓ' ∉ v.M) :
    iota (epsMod v.M) * insSign (v.M.erase ℓ) ℓ +
      iota (epsMod (v.nb ℓ).M) * insSign (v.M.erase ℓ) ℓ' = 0 := by
  have hX5 := orient_card_image_erase_label v hℓ
  have hnb := nb_M_eq v hℓ hℓ' hℓ'v
  have hn1 := orient_label_notMem_image_erase v hℓ
  have hn2 := orient_label_notMem_image_erase_nb v hℓ hℓ' hℓ'v
  have e1 : epsMod v.M =
      labelDet labelRow (insert ℓ.label ((v.M.erase ℓ).image Line.label)) := by
    unfold epsMod
    rw [← Finset.image_insert, Finset.insert_erase hℓ]
  have e2 : epsMod (v.nb ℓ).M =
      labelDet labelRow (insert ℓ'.label ((v.M.erase ℓ).image Line.label)) := by
    unfold epsMod
    rw [hnb, Finset.image_insert]
  have d1 := labelDet_insert labelRow ((v.M.erase ℓ).image Line.label) hX5 ℓ.label hn1
  have d2 := labelDet_insert labelRow ((v.M.erase ℓ).image Line.label) hX5 ℓ'.label hn2
  have hspan : labelRow ℓ'.label + labelRow ℓ.label ∈ Submodule.span (ZMod 3)
      (Set.range (sortedRows labelRow ((v.M.erase ℓ).image Line.label) hX5)) := by
    rw [orient_range_sortedRows]
    exact orient_add_mem_span_rows v hℓ hℓ' hℓ'v
  have hdet : (Matrix.of (Fin.cons (labelRow ℓ'.label)
      (sortedRows labelRow ((v.M.erase ℓ).image Line.label) hX5) : Fin 6 → Fin 6 → ZMod 3)).det =
      -(Matrix.of (Fin.cons (labelRow ℓ.label)
      (sortedRows labelRow ((v.M.erase ℓ).image Line.label) hX5) : Fin 6 → Fin 6 → ZMod 3)).det :=
    det_cons_eq_neg_of_add_mem_span _ _ _ hspan
  have hε1 := e1.trans d1
  have hε2 := e2.trans d2
  rw [hdet] at hε2
  unfold insSign
  exact orient_sign_cancel _ _ _ _ _ hε1 hε2

end TernaryPeriodPolynomials.FreeResolution
