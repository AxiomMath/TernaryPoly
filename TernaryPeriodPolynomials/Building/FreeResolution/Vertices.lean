module

public import TernaryPeriodPolynomials.Building.FreeResolution.A3

@[expose] public section


/-!
# The perfect vertices

Original work by Claude Opus 5.5.

The vertices are the `GL₃(ℤ)`-translates `hᵀ A₀ h` of the perfect form `A₃`. Each vertex `v`
takes values `≥ 1` on nonzero integer vectors and has exactly six minimal lines `M v = h⁻¹ M₀`,
with injective labels. The dual basis `U v ℓ` (`U v ℓ [ℓ'] = δ`) gives the expansion
`Y = ∑_{ℓ ∈ M v} Y[ℓ] • U v ℓ` of every symmetric form, and `v + U v ℓ` is again a vertex, the
neighbour of `v` across the facet opposite `ℓ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

open GeneralEisenstein Matrix

/-! ### Forms on lines -/

/-- The value of a form on a line. -/
def Line.qf (A : Form) : Line → ℚ :=
  Quotient.lift (FreeResolution.qf A) (fun x y h => by
    rcases h with rfl | rfl
    · rfl
    · exact (FreeResolution.qf_neg A x).symm)

theorem Line.qf_mk (A : Form) (x : Vec) :
    Line.qf A (Line.mk x) = FreeResolution.qf A x := rfl

theorem Line.qf_smul (h : IntegralGL3) (A : Form) (ℓ : Line) :
    Line.qf A (h • ℓ) = Line.qf (act h A) ℓ := by
  induction ℓ using Line.ind with | h x => ?_
  rw [smul_mk, Line.qf_mk, Line.qf_mk, FreeResolution.qf_act]

theorem Line.qf_add (A B : Form) (ℓ : Line) :
    Line.qf (A + B) ℓ = Line.qf A ℓ + Line.qf B ℓ := by
  induction ℓ using Line.ind with | h x => ?_
  exact FreeResolution.qf_add A B x

theorem Line.qf_sub (A B : Form) (ℓ : Line) :
    Line.qf (A - B) ℓ = Line.qf A ℓ - Line.qf B ℓ := by
  induction ℓ using Line.ind with | h x => ?_
  exact FreeResolution.qf_sub A B x

theorem Line.qf_smul_form (c : ℚ) (A : Form) (ℓ : Line) :
    Line.qf (c • A) ℓ = c * Line.qf A ℓ := by
  induction ℓ using Line.ind with | h x => ?_
  exact FreeResolution.qf_smul c A x

theorem Line.qf_sum {ι : Type} (s : Finset ι) (A : ι → Form) (ℓ : Line) :
    Line.qf (∑ i ∈ s, A i) ℓ = ∑ i ∈ s, Line.qf (A i) ℓ := by
  induction ℓ using Line.ind with | h x => ?_
  exact FreeResolution.qf_sum s A x

theorem toQ_one : toQ 1 = 1 := by
  ext i j
  by_cases h : i = j <;> simp [toQ, Matrix.one_apply, h]

theorem act_inv_act (h : IntegralGL3) (A : Form) : act h (act h⁻¹ A) = A := by
  rw [act_act, inv_mul_cancel]
  simp [act, toQ_one]

/-! ### The minimal lines of `A₀` -/

/-- The six minimal lines of `A₀`. -/
def M0 : Finset Line := Finset.univ.image fun i : Fin 6 => Line.mk (m i)

theorem mk_m_injective : Function.Injective fun i : Fin 6 => Line.mk (m i) := by
  intro i k h
  by_contra hik
  have hr := m_injective_mod i k hik
  rcases Line.mk_eq_mk.mp h with h1 | h1
  · exact hr.1 (by rw [h1])
  · exact hr.2 (by rw [h1, red_neg])

theorem card_M0 : M0.card = 6 := by
  rw [M0, Finset.card_image_of_injective _ mk_m_injective, Finset.card_univ, Fintype.card_fin]

theorem mem_M0_mk (x : Vec) : Line.mk x ∈ M0 ↔ qf A0 x = 1 := by
  rw [qf_A0_eq_one_iff]
  simp only [M0, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Line.mk_eq_mk.mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Line.mk_eq_mk.mpr hi⟩

theorem mem_M0 (ℓ : Line) : ℓ ∈ M0 ↔ Line.qf A0 ℓ = 1 := by
  induction ℓ using Line.ind with | h x => ?_
  exact mem_M0_mk x

/-- The index of a minimal line of `A₀`. -/
def idx0 (ℓ : Line) : Fin 6 := if h : ∃ i, Line.mk (m i) = ℓ then h.choose else 0

theorem idx0_mk (i : Fin 6) : idx0 (Line.mk (m i)) = i := by
  have h : ∃ k, Line.mk (m k) = Line.mk (m i) := ⟨i, rfl⟩
  rw [idx0, dite_eq_left h]
  exact mk_m_injective h.choose_spec

theorem mk_m_idx0 {ℓ : Line} (hℓ : ℓ ∈ M0) : Line.mk (m (idx0 ℓ)) = ℓ := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hℓ
  rw [idx0_mk]

/-! ### Vertices -/

/-- A vertex: the Gram matrix of a `GL₃(ℤ)`-translate of the perfect form `A₀`. -/
@[ext] structure Vtx where
  /-- The Gram matrix. -/
  gram : Form
  isVertex : ∃ h : IntegralGL3, gram = act h A0

namespace Vtx

/-- A frame of the vertex: `gram = frameᵀ A₀ frame`. -/
def frame (v : Vtx) : IntegralGL3 := v.isVertex.choose

theorem gram_eq (v : Vtx) : v.gram = act v.frame A0 := v.isVertex.choose_spec

theorem gram_transpose (v : Vtx) : v.gramᵀ = v.gram := by
  rw [gram_eq]
  exact act_transpose _ _ A0_transpose

theorem qf_gram (v : Vtx) (x : Vec) : qf v.gram x = qf A0 (mv v.frame x) := by
  rw [gram_eq, qf_act]

theorem mv_ne_zero (h : IntegralGL3) {x : Vec} (hx : x ≠ 0) : mv h x ≠ 0 := by
  intro h0
  apply hx
  have := congrArg (mv h⁻¹) h0
  rwa [mv_inv_mv, show mv h⁻¹ 0 = 0 from Matrix.mulVec_zero _] at this

/-- Minimality: every vertex is at least `1` on nonzero integer vectors. -/
theorem qf_ge_one (v : Vtx) {x : Vec} (hx : x ≠ 0) : 1 ≤ qf v.gram x := by
  rw [qf_gram]
  exact qf_A0_ge_one (mv_ne_zero _ hx)

/-- The minimal lines of a vertex. -/
def M (v : Vtx) : Finset Line := M0.image fun ℓ => v.frame⁻¹ • ℓ

theorem mem_M_iff_smul (v : Vtx) (ℓ : Line) : ℓ ∈ v.M ↔ v.frame • ℓ ∈ M0 := by
  constructor
  · intro h
    obtain ⟨ℓ0, h0, rfl⟩ := Finset.mem_image.mp h
    rwa [smul_inv_smul]
  · intro h
    exact Finset.mem_image.mpr ⟨v.frame • ℓ, h, inv_smul_smul _ _⟩

theorem mem_M (v : Vtx) (ℓ : Line) : ℓ ∈ v.M ↔ Line.qf v.gram ℓ = 1 := by
  rw [mem_M_iff_smul, mem_M0, Line.qf_smul, ← gram_eq]

theorem mem_M_mk (v : Vtx) (x : Vec) : Line.mk x ∈ v.M ↔ qf v.gram x = 1 :=
  v.mem_M (Line.mk x)

theorem card_M (v : Vtx) : v.M.card = 6 := by
  rw [M, Finset.card_image_of_injective _ (MulAction.injective _), card_M0]

theorem mk_ne_zero_of_mem (v : Vtx) {x : Vec} (h : Line.mk x ∈ v.M) : x ≠ 0 := by
  rintro rfl
  rw [mem_M_mk, qf_zero_vec] at h
  exact zero_ne_one h

/-- Values of a vertex on lines are at least one, except on the zero line. -/
theorem qf_line_ge_one (v : Vtx) {ℓ : Line} (hℓ : ℓ ≠ Line.mk 0) : 1 ≤ Line.qf v.gram ℓ := by
  induction ℓ using Line.ind with | h x => ?_
  refine v.qf_ge_one fun hx => hℓ ?_
  rw [hx]

theorem ne_zero_line_of_mem {v : Vtx} {ℓ : Line} (h : ℓ ∈ v.M) : ℓ ≠ Line.mk 0 := by
  rintro rfl
  exact v.mk_ne_zero_of_mem h rfl

theorem qf_ge_one_of_mem (v w : Vtx) {ℓ : Line} (h : ℓ ∈ w.M) : 1 ≤ Line.qf v.gram ℓ :=
  v.qf_line_ge_one (ne_zero_line_of_mem h)

theorem sum_M {β : Type} [AddCommMonoid β] (v : Vtx) (F : Line → β) :
    ∑ ℓ ∈ v.M, F ℓ = ∑ i : Fin 6, F (v.frame⁻¹ • Line.mk (m i)) := by
  rw [M, Finset.sum_image (by
      intro a _ b _ h
      exact MulAction.injective _ h),
    M0, Finset.sum_image (by
      intro a _ b _ h
      exact mk_m_injective h)]

theorem mem_M_of_index (v : Vtx) (i : Fin 6) : v.frame⁻¹ • Line.mk (m i) ∈ v.M :=
  Finset.mem_image.mpr ⟨Line.mk (m i), Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩

theorem exists_index (v : Vtx) {ℓ : Line} (h : ℓ ∈ v.M) :
    ∃ i : Fin 6, ℓ = v.frame⁻¹ • Line.mk (m i) := by
  obtain ⟨ℓ0, h0, rfl⟩ := Finset.mem_image.mp h
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h0
  exact ⟨i, rfl⟩

/-! ### The dual basis and the expansion -/

/-- The dual basis of the minimal rank-one forms at a vertex. -/
def U (v : Vtx) (ℓ : Line) : Form := act v.frame (U0 (idx0 (v.frame • ℓ)))

theorem U_transpose (v : Vtx) (ℓ : Line) : (v.U ℓ)ᵀ = v.U ℓ :=
  act_transpose _ _ (U0_transpose _)

theorem U_index (v : Vtx) (i : Fin 6) : v.U (v.frame⁻¹ • Line.mk (m i)) = act v.frame (U0 i) := by
  rw [U, smul_inv_smul, idx0_mk]

theorem qf_U (v : Vtx) {ℓ ℓ' : Line} (hℓ : ℓ ∈ v.M) (hℓ' : ℓ' ∈ v.M) :
    Line.qf (v.U ℓ) ℓ' = if ℓ' = ℓ then 1 else 0 := by
  obtain ⟨i, rfl⟩ := v.exists_index hℓ
  obtain ⟨k, rfl⟩ := v.exists_index hℓ'
  rw [U_index, ← Line.qf_smul, smul_inv_smul, Line.qf_mk, qf_U0]
  by_cases hik : i = k
  · subst hik
    simp
  · rw [ite_eq_right hik, ite_eq_right]
    intro h
    exact hik (mk_m_injective (MulAction.injective _ h)).symm

/-- Every symmetric form is the combination of the dual basis with its values on the minimal
lines. -/
theorem expand (v : Vtx) (Y : Form) (hY : Yᵀ = Y) :
    Y = ∑ ℓ ∈ v.M, Line.qf Y ℓ • v.U ℓ := by
  have hX : (act v.frame⁻¹ Y)ᵀ = act v.frame⁻¹ Y := act_transpose _ _ hY
  have e := expand0 (act v.frame⁻¹ Y) hX
  rw [sum_M]
  conv_lhs => rw [← act_inv_act v.frame Y, e]
  rw [act_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [act_smul, U_index, qf_act, smul_mk, Line.qf_mk]

/-! ### Neighbours -/

theorem isVertex_add_U (v : Vtx) (ℓ : Line) :
    ∃ h : IntegralGL3, v.gram + v.U ℓ = act h A0 := by
  refine ⟨g0 (idx0 (v.frame • ℓ)) * v.frame, ?_⟩
  rw [U, gram_eq, ← act_add, A0_add_U0, act_act]

/-- The neighbour of `v` across the facet opposite `ℓ`. -/
def nb (v : Vtx) (ℓ : Line) : Vtx := ⟨v.gram + v.U ℓ, v.isVertex_add_U ℓ⟩

theorem nb_gram (v : Vtx) (ℓ : Line) : (v.nb ℓ).gram = v.gram + v.U ℓ := rfl

theorem qf_nb_of_mem (v : Vtx) {ℓ ℓ' : Line} (hℓ : ℓ ∈ v.M) (hℓ' : ℓ' ∈ v.M) :
    Line.qf (v.nb ℓ).gram ℓ' = if ℓ' = ℓ then 2 else 1 := by
  rw [nb_gram, Line.qf_add, (v.mem_M ℓ').mp hℓ', v.qf_U hℓ hℓ']
  split_ifs <;> norm_num

theorem mem_nb_of_mem (v : Vtx) {ℓ ℓ' : Line} (hℓ : ℓ ∈ v.M) (hℓ' : ℓ' ∈ v.M) (hne : ℓ' ≠ ℓ) :
    ℓ' ∈ (v.nb ℓ).M := by
  rw [mem_M, v.qf_nb_of_mem hℓ hℓ', ite_eq_right hne]

theorem not_mem_nb (v : Vtx) {ℓ : Line} (hℓ : ℓ ∈ v.M) : ℓ ∉ (v.nb ℓ).M := by
  rw [mem_M, v.qf_nb_of_mem hℓ hℓ, ite_eq_left rfl]
  norm_num

theorem nb_ne (v : Vtx) {ℓ : Line} (hℓ : ℓ ∈ v.M) : v.nb ℓ ≠ v := by
  intro h
  apply v.not_mem_nb hℓ
  rw [h]
  exact hℓ

/-- The new minimal line of the neighbour. -/
theorem mem_nb (v : Vtx) (i : Fin 6) :
    v.frame⁻¹ • Line.mk (mNew i) ∈ (v.nb (v.frame⁻¹ • Line.mk (m i))).M := by
  rw [mem_M, nb_gram, U_index, gram_eq, ← act_add, ← Line.qf_smul, smul_inv_smul, Line.qf_mk,
    qf_neighbour_mNew]

theorem new_not_mem (v : Vtx) (i : Fin 6) : v.frame⁻¹ • Line.mk (mNew i) ∉ v.M := by
  rw [mem_M, gram_eq, ← Line.qf_smul, smul_inv_smul, Line.qf_mk, qf_A0, Q0_mNew]
  norm_num

/-! ### Translating vertices -/

/-- The translate of a vertex by an invertible integral matrix. -/
def translate (k : IntegralGL3) (v : Vtx) : Vtx :=
  ⟨act k⁻¹ v.gram, by
    obtain ⟨h, hh⟩ := v.isVertex
    exact ⟨h * k⁻¹, by rw [hh, act_act]⟩⟩

theorem mem_M_translate (k : IntegralGL3) (v : Vtx) (ℓ : Line) :
    ℓ ∈ (translate k v).M ↔ k⁻¹ • ℓ ∈ v.M := by
  rw [mem_M, mem_M, Line.qf_smul]
  rfl

theorem translate_M (k : IntegralGL3) (v : Vtx) : (translate k v).M = v.M.image (k • ·) := by
  ext ℓ
  rw [mem_M_translate, Finset.mem_image]
  constructor
  · intro h
    exact ⟨k⁻¹ • ℓ, h, smul_inv_smul _ _⟩
  · rintro ⟨ℓ0, h0, rfl⟩
    rwa [inv_smul_smul]

/-! ### Labels and independence on the minimal lines -/

theorem red_index (v : Vtx) (i : Fin 6) :
    red (m i) = ((v.frame : Matrix (Fin 3) (Fin 3) ℤ).map (Int.cast : ℤ → ZMod 3)) *ᵥ
      red (mv v.frame⁻¹ (m i)) := by
  rw [← red_mv, mv_mv_inv]

theorem label_injOn (v : Vtx) : Set.InjOn Line.label (v.M : Set Line) := by
  intro ℓ hℓ ℓ' hℓ' h
  obtain ⟨i, rfl⟩ := v.exists_index hℓ
  obtain ⟨k, rfl⟩ := v.exists_index hℓ'
  rw [smul_mk, smul_mk, Line.label_mk, Line.label_mk] at h
  by_contra hne
  have hik : i ≠ k := by
    rintro rfl
    exact hne rfl
  have hr := m_injective_mod i k hik
  rcases red_of_labelVec h.symm with h1 | h1
  · apply hr.1
    rw [v.red_index k, v.red_index i, h1]
  · apply hr.2
    rw [v.red_index k, v.red_index i, h1, Matrix.mulVec_neg]

theorem red_ne_zero_of_mem (v : Vtx) {x : Vec} (h : Line.mk x ∈ v.M) : red x ≠ 0 := by
  obtain ⟨i, hi⟩ := v.exists_index h
  rw [smul_mk] at hi
  intro h0
  apply red_m_ne_zero i
  rw [v.red_index i]
  rcases Line.mk_eq_mk.mp hi with h1 | h1
  · rw [h1, h0, Matrix.mulVec_zero]
  · rw [h1, red_neg, h0, neg_zero, Matrix.mulVec_zero]

theorem pair_extends_M (v : Vtx) {a b : Line} (ha : a ∈ v.M) (hb : b ∈ v.M) (hab : a ≠ b) :
    ∃ c ∈ v.M, Line.Indep a b c := by
  obtain ⟨i, rfl⟩ := v.exists_index ha
  obtain ⟨k, rfl⟩ := v.exists_index hb
  have hik : i ≠ k := by
    rintro rfl
    exact hab rfl
  obtain ⟨l, hl⟩ := pair_extends i k hik
  refine ⟨v.frame⁻¹ • Line.mk (m l), v.mem_M_of_index l, ?_⟩
  rw [Line.indep_smul, Line.indep_mk]
  exact hl

end Vtx

end TernaryPeriodPolynomials.FreeResolution
