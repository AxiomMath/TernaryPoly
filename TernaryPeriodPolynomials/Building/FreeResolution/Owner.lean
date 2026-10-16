module

public import TernaryPeriodPolynomials.Building.FreeResolution.Finite

@[expose] public section


/-!
# The Morse function on the vertices

Original work by Claude Opus 5.5.

Vertices are ordered by the lexicographic key `(tr A, A₀₀, A₁₁, A₀₁, A₀₂, A₁₂)`, a linear function
of the Gram matrix that is injective on symmetric matrices and whose first coordinate is the
trace; the order is well founded because only finitely many vertices have bounded trace. The
expansion `B − v = ∑_{ℓ ∈ M v} (B[ℓ] − 1) (nb v ℓ − v)` with nonnegative coefficients
(minimality of `B`) is the convexity that makes this a Morse function on the well-rounded
complex:
* the owner (key-maximal vertex) of a spanning set `T` of minimal lines is `v` exactly when every
  neighbour of `v` across a facet not containing `T` is lower;
* the lines of `v` whose neighbours are higher span;
* a vertex all of whose neighbours are higher is the minimum;
* a five-element facet lies in exactly the two vertices `v` and `nb v ℓ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

open GeneralEisenstein Matrix

/-! ### Lexicographic positivity -/

/-- Lexicographic positivity of a vector in `ℚ⁶`. -/
def LexPos (x : Fin 6 → ℚ) : Prop := ∃ i, 0 < x i ∧ ∀ j < i, x j = 0

theorem LexPos.add {x y : Fin 6 → ℚ} (hx : LexPos x) (hy : LexPos y) : LexPos (x + y) := by
  obtain ⟨i, hi, hi0⟩ := hx
  obtain ⟨k, hk, hk0⟩ := hy
  rcases lt_trichotomy i k with h | rfl | h
  · refine ⟨i, ?_, fun j hj => ?_⟩
    · rw [Pi.add_apply, hk0 i h]
      linarith
    · rw [Pi.add_apply, hi0 j hj, hk0 j (hj.trans h), add_zero]
  · refine ⟨i, ?_, fun j hj => ?_⟩
    · rw [Pi.add_apply]
      linarith
    · rw [Pi.add_apply, hi0 j hj, hk0 j hj, add_zero]
  · refine ⟨k, ?_, fun j hj => ?_⟩
    · rw [Pi.add_apply, hi0 k h]
      linarith
    · rw [Pi.add_apply, hi0 j (hj.trans h), hk0 j hj, add_zero]

theorem LexPos.smul {x : Fin 6 → ℚ} (hx : LexPos x) {c : ℚ} (hc : 0 < c) : LexPos (c • x) := by
  obtain ⟨i, hi, hi0⟩ := hx
  refine ⟨i, ?_, fun j hj => ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul]
    exact mul_pos hc hi
  · rw [Pi.smul_apply, hi0 j hj, smul_zero]

theorem not_lexPos_zero : ¬ LexPos 0 := by
  rintro ⟨i, hi, -⟩
  simp at hi

theorem LexPos.not_neg {x : Fin 6 → ℚ} (hx : LexPos x) : ¬ LexPos (-x) := by
  intro h
  have := hx.add h
  rw [add_neg_cancel] at this
  exact not_lexPos_zero this

theorem lexPos_trichotomy (x : Fin 6 → ℚ) : x = 0 ∨ LexPos x ∨ LexPos (-x) := by
  by_cases h : x = 0
  · exact Or.inl h
  · right
    have hne : (Finset.univ.filter fun j => x j ≠ 0).Nonempty := by
      by_contra hc
      apply h
      funext j
      by_contra hj
      exact hc ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    set i := (Finset.univ.filter fun j => x j ≠ 0).min' hne
    have hi : x i ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    have hlow : ∀ j < i, x j = 0 := by
      intro j hj
      by_contra hxj
      have := Finset.min'_le (Finset.univ.filter fun j => x j ≠ 0) j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hxj⟩)
      exact absurd hj (not_lt.mpr this)
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · right
      refine ⟨i, ?_, fun j hj => ?_⟩
      · rw [Pi.neg_apply]
        linarith
      · rw [Pi.neg_apply, hlow j hj, neg_zero]
    · exact Or.inl ⟨i, hpos, hlow⟩

/-- A nonnegative combination of positive vectors is positive unless all coefficients vanish. -/
theorem lexPos_sum {ι : Type} (S : Finset ι) (c : ι → ℚ) (x : ι → Fin 6 → ℚ)
    (h : ∀ i ∈ S, c i = 0 ∨ (0 < c i ∧ LexPos (x i))) :
    (∀ i ∈ S, c i = 0) ∨ LexPos (∑ i ∈ S, c i • x i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    left
    intro i hi
    simp at hi
  · intro a S ha ih h
    have hS : ∀ i ∈ S, c i = 0 ∨ (0 < c i ∧ LexPos (x i)) :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha]
    rcases h a (Finset.mem_insert_self a S) with h0 | ⟨hpos, hx⟩
    · rcases ih hS with h1 | h1
      · left
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact h0
        · exact h1 i hi
      · right
        rw [h0, zero_smul, zero_add]
        exact h1
    · right
      rcases ih hS with h1 | h1
      · have : ∑ i ∈ S, c i • x i = 0 :=
          Finset.sum_eq_zero fun i hi => by rw [h1 i hi, zero_smul]
        rw [this, add_zero]
        exact hx.smul hpos
      · exact (hx.smul hpos).add h1

/-! ### The key -/

/-- The lexicographic key of a form: trace first. -/
def key (A : Form) : Fin 6 → ℚ := ![A 0 0 + A 1 1 + A 2 2, A 0 0, A 1 1, A 0 1, A 0 2, A 1 2]

theorem key_add (A B : Form) : key (A + B) = key A + key B := by
  funext i
  fin_cases i <;> simp [key]
  ring

theorem key_smul (c : ℚ) (A : Form) : key (c • A) = c • key A := by
  funext i
  fin_cases i <;> simp [key]
  ring

theorem key_sub (A B : Form) : key (A - B) = key A - key B := by
  funext i
  fin_cases i <;> simp [key]
  ring

theorem key_zero : key 0 = 0 := by
  funext i
  fin_cases i <;> simp [key]

/-- The key as an additive map. -/
def keyHom : Form →+ (Fin 6 → ℚ) where
  toFun := key
  map_zero' := key_zero
  map_add' := key_add

theorem key_sum {ι : Type} (S : Finset ι) (A : ι → Form) :
    key (∑ i ∈ S, A i) = ∑ i ∈ S, key (A i) :=
  map_sum keyHom A S

theorem key_injective {A B : Form} (hA : Aᵀ = A) (hB : Bᵀ = B) (h : key A = key B) : A = B := by
  have hA' : ∀ i j, A j i = A i j := fun i j => by rw [← Matrix.transpose_apply A i j, hA]
  have hB' : ∀ i j, B j i = B i j := fun i j => by rw [← Matrix.transpose_apply B i j, hB]
  have k0 : A 0 0 + A 1 1 + A 2 2 = B 0 0 + B 1 1 + B 2 2 := congrFun h 0
  have k1 : A 0 0 = B 0 0 := congrFun h 1
  have k2 : A 1 1 = B 1 1 := congrFun h 2
  have k3 : A 0 1 = B 0 1 := congrFun h 3
  have k4 : A 0 2 = B 0 2 := congrFun h 4
  have k5 : A 1 2 = B 1 2 := congrFun h 5
  have a10 := hA' 0 1
  have a20 := hA' 0 2
  have a21 := hA' 1 2
  have b10 := hB' 0 1
  have b20 := hB' 0 2
  have b21 := hB' 1 2
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> decide
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> linarith

/-! ### The order on vertices -/

/-- The strict order of vertices by their keys. -/
def VtxLT (v w : Vtx) : Prop := LexPos (key w.gram - key v.gram)

theorem Vtx.eq_of_key {v w : Vtx} (h : key v.gram = key w.gram) : v = w :=
  Vtx.ext (key_injective v.gram_transpose w.gram_transpose h)

instance : IsStrictTotalOrder Vtx VtxLT where
  trichotomous v w h1 h2 := by
    rcases lexPos_trichotomy (key w.gram - key v.gram) with h | h | h
    · exact Vtx.eq_of_key (sub_eq_zero.mp h).symm
    · exact absurd h h1
    · apply absurd _ h2
      show LexPos (key v.gram - key w.gram)
      rwa [neg_sub] at h
  irrefl v h := by
    rw [VtxLT, sub_self] at h
    exact not_lexPos_zero h
  trans u v w huv hvw := by
    have := LexPos.add hvw huv
    rwa [sub_add_sub_cancel] at this

instance : DecidableRel VtxLT := Classical.decRel _

instance : LinearOrder Vtx := linearOrderOfSTO VtxLT

theorem Vtx.lt_iff (v w : Vtx) : v < w ↔ LexPos (key w.gram - key v.gram) := Iff.rfl

theorem Vtx.trace_le_of_lt {v w : Vtx} (h : v < w) : v.trace ≤ w.trace := by
  obtain ⟨i, hi, hi0⟩ := (Vtx.lt_iff v w).mp h
  have e : ∀ u : Vtx, key u.gram 0 = u.trace := fun u => rfl
  by_cases h0 : i = 0
  · subst h0
    rw [Pi.sub_apply, e, e] at hi
    linarith
  · have := hi0 0 (Fin.pos_iff_ne_zero.mpr h0)
    rw [Pi.sub_apply, e, e] at this
    linarith

theorem Vtx.lower_finite (w : Vtx) : {v : Vtx | v < w}.Finite :=
  (trace_finite w.trace).subset fun _ hv => Vtx.trace_le_of_lt hv

instance : WellFoundedLT Vtx := by
  refine Subrelation.wf (r := fun v w : Vtx => Set.ncard {u : Vtx | u < v} <
      Set.ncard {u : Vtx | u < w}) ?_ (InvImage.wf (fun v : Vtx => Set.ncard {u : Vtx | u < v})
      wellFounded_lt)
  intro v w hvw
  apply Set.ncard_lt_ncard _ (Vtx.lower_finite w)
  refine ⟨fun u hu => lt_trans hu hvw, fun hsub => ?_⟩
  exact lt_irrefl v (hsub (show v ∈ {u : Vtx | u < w} from hvw))

/-! ### The convexity expansion -/

theorem Vtx.key_sub_expand (v B : Vtx) :
    key B.gram - key v.gram =
      ∑ ℓ ∈ v.M, (Line.qf B.gram ℓ - 1) • (key (v.nb ℓ).gram - key v.gram) := by
  have hY : (B.gram - v.gram)ᵀ = B.gram - v.gram := by
    rw [Matrix.transpose_sub, B.gram_transpose, v.gram_transpose]
  have e := v.expand _ hY
  rw [← key_sub, e, key_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [key_smul, Line.qf_sub, (v.mem_M ℓ).mp hℓ, Vtx.nb_gram, ← key_sub, add_sub_cancel_left]

/-- If on every minimal line of `v` the vertex `B` is minimal or the neighbour is lower, then
`B ≤ v`. -/
theorem Vtx.le_of_lines (v B : Vtx) (h : ∀ ℓ ∈ v.M, Line.qf B.gram ℓ = 1 ∨ v.nb ℓ < v) :
    B ≤ v := by
  have e : key v.gram - key B.gram =
      ∑ ℓ ∈ v.M, (Line.qf B.gram ℓ - 1) • (key v.gram - key (v.nb ℓ).gram) := by
    rw [← neg_sub, v.key_sub_expand B, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← smul_neg, neg_sub]
  have hc : ∀ ℓ ∈ v.M, Line.qf B.gram ℓ - 1 = 0 ∨
      (0 < Line.qf B.gram ℓ - 1 ∧ LexPos (key v.gram - key (v.nb ℓ).gram)) := by
    intro ℓ hℓ
    rcases h ℓ hℓ with h1 | h1
    · left
      rw [h1, sub_self]
    · by_cases h2 : Line.qf B.gram ℓ = 1
      · left
        rw [h2, sub_self]
      · right
        have h3 := B.qf_ge_one_of_mem v hℓ
        refine ⟨?_, (Vtx.lt_iff _ _).mp h1⟩
        rcases lt_or_eq_of_le h3 with h4 | h4
        · linarith
        · exact absurd h4.symm h2
  rcases lexPos_sum v.M (fun ℓ => Line.qf B.gram ℓ - 1)
      (fun ℓ => key v.gram - key (v.nb ℓ).gram) hc with h0 | h0
  · have h0' : ∀ ℓ ∈ v.M, Line.qf B.gram ℓ - 1 = 0 := h0
    apply le_of_eq
    apply Vtx.eq_of_key
    have : key B.gram - key v.gram = 0 := by
      rw [v.key_sub_expand B]
      exact Finset.sum_eq_zero fun ℓ hℓ => by rw [h0' ℓ hℓ, zero_smul]
    exact sub_eq_zero.mp this
  · have h0' : LexPos (∑ ℓ ∈ v.M,
        (Line.qf B.gram ℓ - 1) • (key v.gram - key (v.nb ℓ).gram)) := h0
    rw [← e] at h0'
    exact le_of_lt ((Vtx.lt_iff B v).mpr h0')

/-- A vertex all of whose neighbours are higher is the minimum. -/
theorem Vtx.le_of_neighbours_higher (v : Vtx) (h : ∀ ℓ ∈ v.M, v < v.nb ℓ) (B : Vtx) : v ≤ B := by
  have hc : ∀ ℓ ∈ v.M, Line.qf B.gram ℓ - 1 = 0 ∨
      (0 < Line.qf B.gram ℓ - 1 ∧ LexPos (key (v.nb ℓ).gram - key v.gram)) := by
    intro ℓ hℓ
    by_cases h2 : Line.qf B.gram ℓ = 1
    · left
      rw [h2, sub_self]
    · right
      have h3 := B.qf_ge_one_of_mem v hℓ
      refine ⟨?_, (Vtx.lt_iff _ _).mp (h ℓ hℓ)⟩
      rcases lt_or_eq_of_le h3 with h4 | h4
      · linarith
      · exact absurd h4.symm h2
  rcases lexPos_sum v.M (fun ℓ => Line.qf B.gram ℓ - 1)
      (fun ℓ => key (v.nb ℓ).gram - key v.gram) hc with h0 | h0
  · have h0' : ∀ ℓ ∈ v.M, Line.qf B.gram ℓ - 1 = 0 := h0
    apply le_of_eq
    apply Vtx.eq_of_key
    have : key B.gram - key v.gram = 0 := by
      rw [v.key_sub_expand B]
      exact Finset.sum_eq_zero fun ℓ hℓ => by rw [h0' ℓ hℓ, zero_smul]
    exact (sub_eq_zero.mp this).symm
  · have h0' : LexPos (∑ ℓ ∈ v.M,
        (Line.qf B.gram ℓ - 1) • (key (v.nb ℓ).gram - key v.gram)) := h0
    rw [← v.key_sub_expand B] at h0'
    exact le_of_lt ((Vtx.lt_iff v B).mpr h0')

/-! ### Owners -/

/-- The perfect form itself, as a vertex. -/
def Vtx.base : Vtx := ⟨A0, 1, by simp [act, toQ_one]⟩

/-- A simplex: a set of lines minimal for some vertex. -/
def IsSimplex (T : Finset Line) : Prop := ∃ v : Vtx, T ⊆ v.M

open Classical in
/-- The owner of a spanning simplex: the largest vertex for which it is minimal. -/
def owner (T : Finset Line) : Vtx :=
  if h : Spans T ∧ IsSimplex T then
    (vertSet_finite h.1).toFinset.max'
      ⟨Exists.choose h.2, (Set.Finite.mem_toFinset _).mpr (Exists.choose_spec h.2)⟩
  else Vtx.base

theorem owner_spec {T : Finset Line} (hT : Spans T) (hs : IsSimplex T) :
    T ⊆ (owner T).M ∧ ∀ B : Vtx, T ⊆ B.M → B ≤ owner T := by
  rw [owner, dite_eq_left ⟨hT, hs⟩]
  refine ⟨?_, fun B hB => Finset.le_max' _ _ ((Set.Finite.mem_toFinset _).mpr hB)⟩
  have := Finset.max'_mem (vertSet_finite hT).toFinset
    ⟨Exists.choose hs, (Set.Finite.mem_toFinset _).mpr (Exists.choose_spec hs)⟩
  exact (Set.Finite.mem_toFinset _).mp this

theorem owner_eq_of {T : Finset Line} (hT : Spans T) {v : Vtx} (hv : T ⊆ v.M)
    (hB : ∀ B : Vtx, T ⊆ B.M → B ≤ v) : owner T = v := by
  have hs : IsSimplex T := ⟨v, hv⟩
  obtain ⟨h1, h2⟩ := owner_spec hT hs
  exact le_antisymm (hB _ h1) (h2 v hv)

/-- The neighbours across facets not containing `T` are lower than the owner. -/
theorem nb_lt_owner {T : Finset Line} (hT : Spans T) (hs : IsSimplex T) {ℓ : Line}
    (hℓ : ℓ ∈ (owner T).M) (hℓT : ℓ ∉ T) : (owner T).nb ℓ < owner T := by
  obtain ⟨h1, h2⟩ := owner_spec hT hs
  have hsub : T ⊆ ((owner T).nb ℓ).M := by
    intro t ht
    exact (owner T).mem_nb_of_mem hℓ (h1 ht) (fun h => hℓT (h ▸ ht))
  exact lt_of_le_of_ne (h2 _ hsub) ((owner T).nb_ne hℓ)

/-- The characterization of the owner by its lower neighbours. -/
theorem owner_eq_iff {T : Finset Line} (hT : Spans T) {v : Vtx} (hv : T ⊆ v.M) :
    owner T = v ↔ ∀ ℓ ∈ v.M, ℓ ∉ T → v.nb ℓ < v := by
  constructor
  · rintro rfl ℓ hℓ hℓT
    exact nb_lt_owner hT ⟨_, hv⟩ hℓ hℓT
  · intro h
    refine owner_eq_of hT hv fun B hB => v.le_of_lines B fun ℓ hℓ => ?_
    by_cases hℓT : ℓ ∈ T
    · exact Or.inl ((B.mem_M ℓ).mp (hB hℓT))
    · exact Or.inr (h ℓ hℓ hℓT)

/-! ### The ascending lines span -/

/-- The minimal lines of `v` whose neighbours are higher. -/
def Vtx.up (v : Vtx) : Finset Line := v.M.filter fun ℓ => ¬ v.nb ℓ < v

theorem Vtx.up_subset_of_owner {T : Finset Line} (hT : Spans T) (hs : IsSimplex T) :
    (owner T).up ⊆ T := by
  intro ℓ hℓ
  obtain ⟨hℓM, hℓ'⟩ := Finset.mem_filter.mp hℓ
  by_contra hℓT
  exact hℓ' (nb_lt_owner hT hs hℓM hℓT)

/-- The square of a linear form, as a form. -/
def sqForm (φ : Vec) : Form := Matrix.of fun i j => (φ i : ℚ) * (φ j : ℚ)

theorem qf_sqForm (φ x : Vec) : qf (sqForm φ) x = ((∑ i, φ i * x i : ℤ) : ℚ) ^ 2 := by
  simp only [qf, sqForm, Matrix.of_apply, Fin.sum_univ_three]
  push_cast
  ring

theorem sqForm_transpose (φ : Vec) : (sqForm φ)ᵀ = sqForm φ := by
  ext i j
  simp only [sqForm, Matrix.transpose_apply, Matrix.of_apply]
  ring

theorem Vtx.up_spans (v : Vtx) : Spans v.up := by
  by_contra hns
  -- two distinct lines of `v` such that `up` lies in their plane
  obtain ⟨a, ha, b, hb, hab, hplane⟩ : ∃ a ∈ v.M, ∃ b ∈ v.M, a ≠ b ∧
      ∀ c ∈ v.up, ¬ Line.Indep a b c := by
    by_cases h2 : ∃ a ∈ v.up, ∃ b ∈ v.up, a ≠ b
    · obtain ⟨a, ha, b, hb, hab⟩ := h2
      exact ⟨a, (Finset.mem_filter.mp ha).1, b, (Finset.mem_filter.mp hb).1, hab,
        fun c hc hi => hns ⟨a, ha, b, hb, c, hc, hi⟩⟩
    · push Not at h2
      obtain ⟨a, ha, hall⟩ : ∃ a ∈ v.M, ∀ c ∈ v.up, c = a := by
        by_cases hne : v.up.Nonempty
        · obtain ⟨a, ha⟩ := hne
          exact ⟨a, (Finset.mem_filter.mp ha).1, fun c hc => h2 c hc a ha⟩
        · have hM : v.M.Nonempty := by
            rw [← Finset.card_pos, v.card_M]
            norm_num
          obtain ⟨a, ha⟩ := hM
          refine ⟨a, ha, fun c hc => absurd ⟨c, hc⟩ hne⟩
      obtain ⟨b, hb, hba⟩ : ∃ b ∈ v.M, b ≠ a := by
        by_contra hc
        push Not at hc
        have : v.M ⊆ {a} := fun x hx => Finset.mem_singleton.mpr (hc x hx)
        have := Finset.card_le_card this
        rw [v.card_M, Finset.card_singleton] at this
        norm_num at this
      refine ⟨a, ha, b, hb, hba.symm, fun c hc hi => ?_⟩
      rw [hall c hc] at hi
      exact hi (det3v_self_outer _ _)
  obtain ⟨c, hc, habc⟩ := v.pair_extends_M ha hb hab
  have hsq : ∀ ℓ : Line, Line.qf (sqForm (cross (Quotient.out a) (Quotient.out b))) ℓ =
      ((det3v (Quotient.out a) (Quotient.out b) (Quotient.out ℓ) : ℤ) : ℚ) ^ 2 := by
    intro ℓ
    rw [← Line.mk_out ℓ, Line.qf_mk, qf_sqForm, cross_dot, Line.mk_out]
  have hX : Line.qf (sqForm (cross (Quotient.out a) (Quotient.out b))) c ≠ 0 := by
    rw [hsq]
    have : (det3v (Quotient.out a) (Quotient.out b) (Quotient.out c) : ℚ) ≠ 0 := by
      exact_mod_cast habc
    exact pow_ne_zero 2 this
  have hup : ∀ ℓ ∈ v.up, Line.qf (sqForm (cross (Quotient.out a) (Quotient.out b))) ℓ = 0 := by
    intro ℓ hℓ
    rw [hsq]
    have h0 : det3v (Quotient.out a) (Quotient.out b) (Quotient.out ℓ) = 0 := by
      by_contra hne
      exact hplane ℓ hℓ hne
    rw [h0]
    norm_num
  have e := v.expand (sqForm (cross (Quotient.out a) (Quotient.out b))) (sqForm_transpose _)
  have ekey : -key (sqForm (cross (Quotient.out a) (Quotient.out b))) =
      ∑ ℓ ∈ v.M, Line.qf (sqForm (cross (Quotient.out a) (Quotient.out b))) ℓ •
        (key v.gram - key (v.nb ℓ).gram) := by
    conv_lhs => rw [e]
    rw [key_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [key_smul, Vtx.nb_gram, key_add, sub_add_cancel_left, smul_neg]
  have hc' : ∀ ℓ ∈ v.M, Line.qf (sqForm (cross (Quotient.out a) (Quotient.out b))) ℓ = 0 ∨
      (0 < Line.qf (sqForm (cross (Quotient.out a) (Quotient.out b))) ℓ ∧
        LexPos (key v.gram - key (v.nb ℓ).gram)) := by
    intro ℓ hℓ
    by_cases hu : ℓ ∈ v.up
    · exact Or.inl (hup ℓ hu)
    · have hlt : v.nb ℓ < v := by
        by_contra hn
        exact hu (Finset.mem_filter.mpr ⟨hℓ, hn⟩)
      by_cases h0 : Line.qf (sqForm (cross (Quotient.out a) (Quotient.out b))) ℓ = 0
      · exact Or.inl h0
      · right
        refine ⟨?_, (Vtx.lt_iff _ _).mp hlt⟩
        rw [hsq] at h0 ⊢
        exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm h0)
  have hpos : LexPos (key (sqForm (cross (Quotient.out a) (Quotient.out b)))) := by
    set φ := cross (Quotient.out a) (Quotient.out b)
    refine ⟨0, ?_, fun j hj => absurd hj (Fin.not_lt_zero j)⟩
    have h1 : key (sqForm φ) 0 = (φ 0 : ℚ) ^ 2 + (φ 1 : ℚ) ^ 2 + (φ 2 : ℚ) ^ 2 := by
      show (φ 0 : ℚ) * (φ 0 : ℚ) + (φ 1 : ℚ) * (φ 1 : ℚ) + (φ 2 : ℚ) * (φ 2 : ℚ) = _
      ring
    rw [h1]
    have hφ : φ ≠ 0 := by
      intro h0
      apply hX
      rw [← Line.mk_out c, Line.qf_mk, qf_sqForm, h0]
      simp
    have : (φ 0 : ℚ) ≠ 0 ∨ (φ 1 : ℚ) ≠ 0 ∨ (φ 2 : ℚ) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hφ
      funext i
      fin_cases i
      · exact_mod_cast hcon.1
      · exact_mod_cast hcon.2.1
      · exact_mod_cast hcon.2.2
    have n0 := sq_nonneg (φ 0 : ℚ)
    have n1 := sq_nonneg (φ 1 : ℚ)
    have n2 := sq_nonneg (φ 2 : ℚ)
    rcases this with h | h | h
    · have := lt_of_le_of_ne n0 (Ne.symm (pow_ne_zero 2 h))
      linarith
    · have := lt_of_le_of_ne n1 (Ne.symm (pow_ne_zero 2 h))
      linarith
    · have := lt_of_le_of_ne n2 (Ne.symm (pow_ne_zero 2 h))
      linarith
  rcases lexPos_sum v.M (fun ℓ => Line.qf (sqForm (cross (Quotient.out a) (Quotient.out b))) ℓ)
      (fun ℓ => key v.gram - key (v.nb ℓ).gram) hc' with h0 | h0
  · have h0' : ∀ ℓ ∈ v.M, Line.qf (sqForm (cross (Quotient.out a) (Quotient.out b))) ℓ = 0 :=
      h0
    have : key (sqForm (cross (Quotient.out a) (Quotient.out b))) = 0 := by
      rw [← neg_neg (key _), ekey, Finset.sum_eq_zero fun ℓ hℓ => by rw [h0' ℓ hℓ, zero_smul],
        neg_zero]
    rw [this] at hpos
    exact not_lexPos_zero hpos
  · have h0' : LexPos (∑ ℓ ∈ v.M, Line.qf (sqForm (cross (Quotient.out a) (Quotient.out b))) ℓ •
        (key v.gram - key (v.nb ℓ).gram)) := h0
    rw [← ekey] at h0'
    exact hpos.not_neg h0'

/-! ### Edges -/

theorem Vtx.gram_eq_add_of_facet (v : Vtx) {ℓ : Line} (hℓ : ℓ ∈ v.M) (B : Vtx)
    (hB : v.M.erase ℓ ⊆ B.M) :
    B.gram = v.gram + (Line.qf B.gram ℓ - 1) • v.U ℓ := by
  have hY : (B.gram - v.gram)ᵀ = B.gram - v.gram := by
    rw [Matrix.transpose_sub, B.gram_transpose, v.gram_transpose]
  have e := v.expand _ hY
  rw [Finset.sum_eq_single ℓ] at e
  · rw [Line.qf_sub, (v.mem_M ℓ).mp hℓ] at e
    rw [← e]
    abel
  · intro ℓ' hℓ' hne
    rw [Line.qf_sub, (v.mem_M ℓ').mp hℓ',
      (B.mem_M ℓ').mp (hB (Finset.mem_erase.mpr ⟨hne, hℓ'⟩)), sub_self, zero_smul]
  · intro h
    exact absurd hℓ h

/-- A facet of a vertex lies in exactly two vertices. -/
theorem Vtx.eq_or_eq_nb_of_facet (v : Vtx) {ℓ : Line} (hℓ : ℓ ∈ v.M) (B : Vtx)
    (hB : v.M.erase ℓ ⊆ B.M) : B = v ∨ B = v.nb ℓ := by
  have hg := v.gram_eq_add_of_facet hℓ B hB
  set c := Line.qf B.gram ℓ - 1 with hcdef
  have qB : ∀ x, Line.qf B.gram x = Line.qf v.gram x + c * Line.qf (v.U ℓ) x := by
    intro x
    rw [hg, Line.qf_add, Line.qf_smul_form]
  have qn : ∀ x, Line.qf (v.nb ℓ).gram x = Line.qf v.gram x + Line.qf (v.U ℓ) x := by
    intro x
    rw [Vtx.nb_gram, Line.qf_add]
  by_cases hc0 : c = 0
  · left
    apply Vtx.ext
    rw [hg, hc0, zero_smul, add_zero]
  right
  have hcpos : 0 < c := by
    have := B.qf_ge_one_of_mem v hℓ
    rcases lt_or_eq_of_le this with h | h
    · rw [hcdef]
      linarith
    · exact absurd (by rw [hcdef, ← h, sub_self]) hc0
  obtain ⟨i, hi⟩ := v.exists_index hℓ
  have hn1 : v.frame⁻¹ • Line.mk (mNew i) ∈ (v.nb ℓ).M := by
    rw [hi]
    exact v.mem_nb i
  have hn2 := v.new_not_mem i
  have qvn : 1 < Line.qf v.gram (v.frame⁻¹ • Line.mk (mNew i)) := by
    rcases lt_or_eq_of_le (v.qf_ge_one_of_mem _ hn1) with h | h
    · exact h
    · exact absurd ((v.mem_M _).mpr h.symm) hn2
  have h1 : Line.qf v.gram (v.frame⁻¹ • Line.mk (mNew i)) +
      Line.qf (v.U ℓ) (v.frame⁻¹ • Line.mk (mNew i)) = 1 := by
    rw [← qn]
    exact ((v.nb ℓ).mem_M _).mp hn1
  have h2 : 1 ≤ Line.qf v.gram (v.frame⁻¹ • Line.mk (mNew i)) +
      c * Line.qf (v.U ℓ) (v.frame⁻¹ • Line.mk (mNew i)) := by
    rw [← qB]
    exact B.qf_ge_one_of_mem _ hn1
  have hlt : (v.M.erase ℓ).card < B.M.card := by
    rw [Finset.card_erase_of_mem hℓ, v.card_M, B.card_M]
    norm_num
  obtain ⟨ℓB, hℓB, hℓB'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hℓBv : ℓB ∉ v.M := by
    intro hmem
    apply hℓB'
    refine Finset.mem_erase.mpr ⟨fun h => ?_, hmem⟩
    have := (B.mem_M ℓB).mp hℓB
    rw [h] at this
    apply hc0
    rw [hcdef, this, sub_self]
  have qvB : 1 < Line.qf v.gram ℓB := by
    rcases lt_or_eq_of_le (v.qf_ge_one_of_mem _ hℓB) with h | h
    · exact h
    · exact absurd ((v.mem_M ℓB).mpr h.symm) hℓBv
  have h3 : Line.qf v.gram ℓB + c * Line.qf (v.U ℓ) ℓB = 1 := by
    rw [← qB]
    exact (B.mem_M ℓB).mp hℓB
  have h4 : 1 ≤ Line.qf v.gram ℓB + Line.qf (v.U ℓ) ℓB := by
    rw [← qn]
    exact (v.nb ℓ).qf_ge_one_of_mem _ hℓB
  have hc1 : c = 1 := by
    have un : Line.qf (v.U ℓ) (v.frame⁻¹ • Line.mk (mNew i)) < 0 := by linarith
    have uB : Line.qf (v.U ℓ) ℓB < 0 := by
      by_contra hcon
      push Not at hcon
      have : 0 ≤ c * Line.qf (v.U ℓ) ℓB := mul_nonneg hcpos.le hcon
      linarith
    have le1 : c ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have : (c - 1) * Line.qf (v.U ℓ) (v.frame⁻¹ • Line.mk (mNew i)) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) un
      linarith [show (c - 1) * Line.qf (v.U ℓ) (v.frame⁻¹ • Line.mk (mNew i)) =
        (Line.qf v.gram (v.frame⁻¹ • Line.mk (mNew i)) +
          c * Line.qf (v.U ℓ) (v.frame⁻¹ • Line.mk (mNew i))) -
        (Line.qf v.gram (v.frame⁻¹ • Line.mk (mNew i)) +
          Line.qf (v.U ℓ) (v.frame⁻¹ • Line.mk (mNew i))) by ring]
    have ge1 : 1 ≤ c := by
      by_contra hcon
      push Not at hcon
      have : (1 - c) * Line.qf (v.U ℓ) ℓB < 0 := mul_neg_of_pos_of_neg (by linarith) uB
      linarith [show (1 - c) * Line.qf (v.U ℓ) ℓB =
        (Line.qf v.gram ℓB + Line.qf (v.U ℓ) ℓB) - (Line.qf v.gram ℓB + c * Line.qf (v.U ℓ) ℓB) by
          ring]
    linarith
  apply Vtx.ext
  rw [hg, hc1, one_smul, Vtx.nb_gram]

end TernaryPeriodPolynomials.FreeResolution
