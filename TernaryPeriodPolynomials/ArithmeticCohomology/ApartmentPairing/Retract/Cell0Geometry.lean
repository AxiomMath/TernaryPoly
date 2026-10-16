module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellChains

@[expose] public section


/-!
# The standard top cell of the well-rounded retract

The standard top cell `T₀ = {e₀, e₁, e₂}` of the `wellRounded` complex has exactly sixteen vertices
(`vertFin_T0`, `vtx16`): the Gram matrices with unit diagonal and off-diagonal entries
`(r₁₂, r₁₃, r₂₃) ∈ {0, ±½}³` of determinant `½` (twelve with one zero entry, four with all entries
`±½` and positive product). Their barycentre is the identity form (`bptMat_T0`), i.e. the base point
(the apex of the cone recursion of `ConeRecursion`) of the top cell is the identity. A diagonal form
in the reach of any cell forces the cell to be `T₀` and the form to be the identity
(`flat_reach`): the diagonal flat meets the retract only at the identity form, inside `T₀`.

Formalized by Claude Sonnet 5.5.
-/

open TernaryPeriodPolynomials.FreeResolution Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry

/-- The unit-diagonal Gram matrix with off-diagonal entries `r₁₂, r₁₃, r₂₃`. -/
def gram3 (a b c : ℚ) : Form := !![1, a, b; a, 1, c; b, c, 1]

/-- The first standard basis vector, as an integer vector. -/
def e0 : Vec := ![1, 0, 0]
def e1 : Vec := ![0, 1, 0]
def e2 : Vec := ![0, 0, 1]

/-- The lines of the standard top cell `T₀ = {e₀, e₁, e₂}`. -/
def T0set : Finset Line := {Line.mk e0, Line.mk e1, Line.mk e2}

theorem T0_sub_base : T0set ⊆ Vtx.base.M := by
  intro ℓ hℓ
  simp only [T0set, Finset.mem_insert, Finset.mem_singleton] at hℓ
  rcases hℓ with rfl | rfl | rfl <;>
    (rw [Vtx.mem_M_mk]; change qf A0 _ = 1; simp [qf, A0, e0, e1, e2, Fin.sum_univ_three])

theorem T0_spans : Spans T0set :=
  ⟨Line.mk e0, by simp [T0set], Line.mk e1, by simp [T0set], Line.mk e2, by simp [T0set],
    (Line.indep_mk _ _ _).mpr (by simp [det3v, e0, e1, e2])⟩

/-- The standard top cell. -/
def T0 : Cell := ⟨T0set, T0_spans, Vtx.base, T0_sub_base⟩

def triples : Fin 16 → ℚ × ℚ × ℚ :=
  ![((-1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)),
   ((-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)),
   ((-1 / 2 : ℚ), (0 : ℚ), (-1 / 2 : ℚ)),
   ((-1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)),
   ((-1 / 2 : ℚ), (1 / 2 : ℚ), (-1 / 2 : ℚ)),
   ((-1 / 2 : ℚ), (1 / 2 : ℚ), (0 : ℚ)),
   ((0 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)),
   ((0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)),
   ((0 : ℚ), (1 / 2 : ℚ), (-1 / 2 : ℚ)),
   ((0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)),
   ((1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)),
   ((1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)),
   ((1 / 2 : ℚ), (0 : ℚ), (-1 / 2 : ℚ)),
   ((1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)),
   ((1 / 2 : ℚ), (1 / 2 : ℚ), (0 : ℚ)),
   ((1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ))]

theorem frame_exists (k : Fin 16) : ∃ h : GeneralEisenstein.IntegralGL3, act h A0 = gram3 (triples k).1 (triples k).2.1 (triples k).2.2 := by
  fin_cases k
  · refine ⟨⟨!![-1, 0, 1; 0, 0, -1; 0, 1, 0], !![-1, -1, 0; 0, 0, 1; 0, -1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, 0, 0; 0, 0, 1; 0, 1, 0], !![-1, 0, 0; 0, 0, 1; 0, 1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, 0, 0; 0, 0, 1; 0, 1, -1], !![-1, 0, 0; 0, 1, 1; 0, 1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, 0, 0; 0, 0, -1; 0, 1, 1], !![-1, 0, 0; 0, 1, 1; 0, -1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, 0, 0; 0, 0, -1; 0, 1, 0], !![-1, 0, 0; 0, 0, 1; 0, -1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, 0, -1; 0, 0, 1; 0, 1, 0], !![-1, -1, 0; 0, 0, 1; 0, 1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, 0, 0; 0, -1, 1; 0, 1, 0], !![-1, 0, 0; 0, 0, 1; 0, 1, 1], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, 0, 0; 0, -1, 0; 0, 1, 1], !![-1, 0, 0; 0, -1, 0; 0, 1, 1], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, 0, -1; 0, -1, 1; 0, 1, 0], !![-1, -1, -1; 0, 0, 1; 0, 1, 1], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, 0, -1; 0, -1, 0; 0, 1, 1], !![-1, -1, -1; 0, -1, 0; 0, 1, 1], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, -1, 1; 0, 0, -1; 0, 1, 0], !![-1, -1, -1; 0, 0, 1; 0, -1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, -1, 0; 0, 0, 1; 0, 1, 0], !![-1, 0, -1; 0, 0, 1; 0, 1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, -1, 0; 0, 0, 1; 0, 1, -1], !![-1, -1, -1; 0, 1, 1; 0, 1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, -1, 0; 0, 0, -1; 0, 1, 1], !![-1, -1, -1; 0, 1, 1; 0, -1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, -1, 0; 0, 0, -1; 0, 1, 0], !![-1, 0, -1; 0, 0, 1; 0, -1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · refine ⟨⟨!![-1, -1, -1; 0, 0, 1; 0, 1, 0], !![-1, -1, -1; 0, 0, 1; 0, 1, 0], by decide +kernel, by decide +kernel⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [act, toQ, A0, triples, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem qf_gram_int (v : Vtx) (x : Vec) : ∃ N : ℤ, qf v.gram x = N :=
  ⟨Q0 (mv v.frame x), by rw [Vtx.qf_gram, qf_A0]⟩

theorem gram_symm (v : Vtx) (i j : Fin 3) : v.gram j i = v.gram i j := by
  have h := congrFun (congrFun v.gram_transpose i) j
  simpa using h

theorem diag_of_mem (v : Vtx) (h : T0.val ⊆ v.M) :
    v.gram 0 0 = 1 ∧ v.gram 1 1 = 1 ∧ v.gram 2 2 = 1 := by
  have h0 : Line.mk e0 ∈ v.M := h (by simp [T0, T0set])
  have h1 : Line.mk e1 ∈ v.M := h (by simp [T0, T0set])
  have h2 : Line.mk e2 ∈ v.M := h (by simp [T0, T0set])
  rw [Vtx.mem_M_mk] at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩
  · simpa [qf, e0, Fin.sum_univ_three] using h0
  · simpa [qf, e1, Fin.sum_univ_three] using h1
  · simpa [qf, e2, Fin.sum_univ_three] using h2

theorem half_of_pair (v : Vtx) (x y : Vec) (hx : x ≠ 0) (hy : y ≠ 0)
    (hs : qf v.gram x + qf v.gram y = 4) :
    qf v.gram x = 1 ∨ qf v.gram x = 2 ∨ qf v.gram x = 3 := by
  obtain ⟨N, hN⟩ := qf_gram_int v x
  obtain ⟨M, hM⟩ := qf_gram_int v y
  have h1 := Vtx.qf_ge_one v hx
  have h2 := Vtx.qf_ge_one v hy
  rw [hN] at h1 hs ⊢
  rw [hM] at h2 hs
  have h1' : 1 ≤ N := by exact_mod_cast h1
  have h2' : 1 ≤ M := by exact_mod_cast h2
  have h3 : N + M = 4 := by exact_mod_cast hs
  have : N = 1 ∨ N = 2 ∨ N = 3 := by omega
  rcases this with rfl | rfl | rfl <;> simp

theorem offdiag_cases (v : Vtx) (h : T0.val ⊆ v.M) :
    (v.gram 0 1 = -1 / 2 ∨ v.gram 0 1 = 0 ∨ v.gram 0 1 = 1 / 2) ∧
    (v.gram 0 2 = -1 / 2 ∨ v.gram 0 2 = 0 ∨ v.gram 0 2 = 1 / 2) ∧
    (v.gram 1 2 = -1 / 2 ∨ v.gram 1 2 = 0 ∨ v.gram 1 2 = 1 / 2) := by
  obtain ⟨d0, d1, d2⟩ := diag_of_mem v h
  have s01 := gram_symm v 0 1
  have s02 := gram_symm v 0 2
  have s12 := gram_symm v 1 2
  refine ⟨?_, ?_, ?_⟩
  · have hp := half_of_pair v ![1, 1, 0] ![1, -1, 0] (by simp [funext_iff, Fin.forall_fin_succ])
      (by simp [funext_iff, Fin.forall_fin_succ]) (by
        simp [qf, Fin.sum_univ_three, d0, d1, s01]; ring)
    simp [qf, Fin.sum_univ_three, d0, d1, s01] at hp
    rcases hp with hp | hp | hp
    · left; linarith
    · right; left; linarith
    · right; right; linarith
  · have hp := half_of_pair v ![1, 0, 1] ![1, 0, -1] (by simp [funext_iff, Fin.forall_fin_succ])
      (by simp [funext_iff, Fin.forall_fin_succ]) (by
        simp [qf, Fin.sum_univ_three, d0, d2, s02]; ring)
    simp [qf, Fin.sum_univ_three, d0, d2, s02] at hp
    rcases hp with hp | hp | hp
    · left; linarith
    · right; left; linarith
    · right; right; linarith
  · have hp := half_of_pair v ![0, 1, 1] ![0, 1, -1] (by simp [funext_iff, Fin.forall_fin_succ])
      (by simp [funext_iff, Fin.forall_fin_succ]) (by
        simp [qf, Fin.sum_univ_three, d1, d2, s12]; ring)
    simp [qf, Fin.sum_univ_three, d1, d2, s12] at hp
    rcases hp with hp | hp | hp
    · left; linarith
    · right; left; linarith
    · right; right; linarith

theorem det_gram (v : Vtx) : v.gram.det = 1 / 2 := by
  have hu : IsUnit ((v.frame : Matrix (Fin 3) (Fin 3) ℤ).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp v.frame.isUnit
  have hd : (v.frame : Matrix (Fin 3) (Fin 3) ℤ).det = 1 ∨
      (v.frame : Matrix (Fin 3) (Fin 3) ℤ).det = -1 := Int.isUnit_iff.mp hu
  have htq : (toQ v.frame).det = (((v.frame : Matrix (Fin 3) (Fin 3) ℤ).det : ℤ) : ℚ) := by
    change ((Int.castRingHom ℚ).mapMatrix (v.frame : Matrix (Fin 3) (Fin 3) ℤ)).det = _
    rw [← RingHom.map_det]
    rfl
  have hA : A0.det = 1 / 2 := by
    simp [A0, Matrix.det_fin_three]; norm_num
  rw [Vtx.gram_eq, act, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, htq, hA]
  rcases hd with hd | hd <;> rw [hd] <;> norm_num

theorem gram_eq_gram3 (v : Vtx) (h : T0.val ⊆ v.M) :
    v.gram = gram3 (v.gram 0 1) (v.gram 0 2) (v.gram 1 2) := by
  obtain ⟨d0, d1, d2⟩ := diag_of_mem v h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram3, d0, d1, d2, gram_symm v 0 1, gram_symm v 0 2, gram_symm v 1 2]

theorem gram_of_mem_T0 (v : Vtx) (h : T0.val ⊆ v.M) : ∃ k : Fin 16, v.gram = gram3 (triples k).1 (triples k).2.1 (triples k).2.2 := by
  obtain ⟨ha, hb, hc⟩ := offdiag_cases v h
  have hdet := det_gram v
  rw [gram_eq_gram3 v h] at hdet
  rw [gram_eq_gram3 v h]
  generalize v.gram 0 1 = a at *
  generalize v.gram 0 2 = b at *
  generalize v.gram 1 2 = c at *
  simp only [gram3, Matrix.det_fin_three] at hdet
  simp at hdet
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;>
    first
    | (exfalso; norm_num at hdet; done)
    | (exact (by decide +kernel))

open TernaryPeriodPolynomials.Argument.Lemma33.Retract

/-- The sixteen vertices of the standard top cell. -/
def vtx16 (k : Fin 16) : Vtx :=
  ⟨gram3 (triples k).1 (triples k).2.1 (triples k).2.2, (frame_exists k).choose,
    ((frame_exists k).choose_spec).symm⟩

theorem triples_injective : Function.Injective triples := by
  have : ∀ k k' : Fin 16, triples k = triples k' → k = k' := by decide +kernel
  exact fun k k' h => this k k' h

theorem vtx16_injective : Function.Injective vtx16 := by
  intro k k' h
  apply triples_injective
  have hg : gram3 (triples k).1 (triples k).2.1 (triples k).2.2 =
      gram3 (triples k').1 (triples k').2.1 (triples k').2.2 := congrArg Vtx.gram h
  have h01 := congrFun (congrFun hg 0) 1
  have h02 := congrFun (congrFun hg 0) 2
  have h12 := congrFun (congrFun hg 1) 2
  simp [gram3] at h01 h02 h12
  exact Prod.ext h01 (Prod.ext h02 h12)

theorem T0_sub_M_vtx16 (k : Fin 16) : T0.val ⊆ (vtx16 k).M := by
  intro ℓ hℓ
  simp only [T0, T0set, Finset.mem_insert, Finset.mem_singleton] at hℓ
  rcases hℓ with rfl | rfl | rfl <;>
    (rw [Vtx.mem_M_mk]; simp [vtx16, qf, gram3, e0, e1, e2, Fin.sum_univ_three])

theorem vertFin_T0 : vertFin T0 = Finset.univ.image vtx16 := by
  ext v
  rw [mem_vertFin, Finset.mem_image]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := gram_of_mem_T0 v h
    exact ⟨k, Finset.mem_univ _, (Vtx.ext hk).symm⟩
  · rintro ⟨k, -, rfl⟩
    exact T0_sub_M_vtx16 k

theorem card_vertFin_T0 : (vertFin T0).card = 16 := by
  rw [vertFin_T0, Finset.card_image_of_injective _ vtx16_injective]
  simp

/-- **The base point of the standard top cell is the identity form.** -/
theorem bptMat_T0 : bptMat T0 = 1 := by
  unfold bptMat
  rw [card_vertFin_T0, vertFin_T0, Finset.sum_image (fun a _ b _ h => vtx16_injective h)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, formR, vtx16, gram3, triples] <;> norm_num

theorem bpt_T0 : (bpt T0).1 = 1 := bptMat_T0

/-- A real symmetric matrix is diagonal. -/
def IsDiagMat (M : Mat) : Prop := ∀ i j, i ≠ j → M i j = 0

theorem convex_qfR_eq_one (x : Vec) : Convex ℝ {M : Mat | qfR M x = 1} := by
  intro a ha b hb s t hs ht hst
  have e : qfR (s • a + t • b) x = s * qfR a x + t * qfR b x := by
    simp only [qfR, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    ring_nf
  change qfR (s • a + t • b) x = 1
  rw [e]
  have ha' : qfR a x = 1 := ha
  have hb' : qfR b x = 1 := hb
  rw [ha', hb']
  linarith

/-- The minimal lines of the cell are minimal for every point of its reach. -/
theorem qfR_eq_one_of_reach (C : Cell) {p : PDMat} (hp : p ∈ reach C) {x : Vec}
    (hx : Line.mk x ∈ C.val) : qfR p.1 x = 1 := by
  have hsub : (fun v : Vtx => formR v.gram) '' {v | C.val ⊆ v.M} ⊆ {M : Mat | qfR M x = 1} := by
    rintro _ ⟨v, hv, rfl⟩
    change qfR (formR v.gram) x = 1
    rw [qfR_formR]
    have := (Vtx.mem_M_mk v x).mp (hv hx)
    exact_mod_cast this
  exact convexHull_min hsub (convex_qfR_eq_one x) hp

theorem qfR_diag (M : Mat) (hM : IsDiagMat M) (x : Vec) :
    qfR M x = M 0 0 * (x 0 : ℝ) ^ 2 + M 1 1 * (x 1 : ℝ) ^ 2 + M 2 2 * (x 2 : ℝ) ^ 2 := by
  simp [qfR, Fin.sum_univ_three, hM 0 1 (by decide), hM 0 2 (by decide), hM 1 0 (by decide),
    hM 1 2 (by decide), hM 2 0 (by decide), hM 2 1 (by decide)]
  ring

theorem eq_e0_iff (x : Vec) : x = e0 ↔ x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 0 := by
  constructor
  · rintro rfl; simp [e0]
  · rintro ⟨a, b, c⟩; funext i; fin_cases i <;> simp [e0, a, b, c]

theorem eq_neg_e0_iff (x : Vec) : x = -e0 ↔ x 0 = -1 ∧ x 1 = 0 ∧ x 2 = 0 := by
  constructor
  · rintro rfl; simp [e0]
  · rintro ⟨a, b, c⟩; funext i; fin_cases i <;> simp [e0, a, b, c]

theorem eq_e1_iff (x : Vec) : x = e1 ↔ x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 0 := by
  constructor
  · rintro rfl; simp [e1]
  · rintro ⟨a, b, c⟩; funext i; fin_cases i <;> simp [e1, a, b, c]

theorem eq_neg_e1_iff (x : Vec) : x = -e1 ↔ x 0 = 0 ∧ x 1 = -1 ∧ x 2 = 0 := by
  constructor
  · rintro rfl; simp [e1]
  · rintro ⟨a, b, c⟩; funext i; fin_cases i <;> simp [e1, a, b, c]

theorem eq_e2_iff (x : Vec) : x = e2 ↔ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 1 := by
  constructor
  · rintro rfl; simp [e2]
  · rintro ⟨a, b, c⟩; funext i; fin_cases i <;> simp [e2, a, b, c]

theorem eq_neg_e2_iff (x : Vec) : x = -e2 ↔ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = -1 := by
  constructor
  · rintro rfl; simp [e2]
  · rintro ⟨a, b, c⟩; funext i; fin_cases i <;> simp [e2, a, b, c]


/-- A minimal vector of a diagonal form with diagonal entries `≥ 1` is a coordinate vector. -/
theorem diag_minimal (a0 a1 a2 : ℝ) (h0 : 1 ≤ a0) (h1 : 1 ≤ a1) (h2 : 1 ≤ a2) (x : Vec) (hx : x ≠ 0)
    (hq : a0 * (x 0 : ℝ) ^ 2 + a1 * (x 1 : ℝ) ^ 2 + a2 * (x 2 : ℝ) ^ 2 = 1) :
    (a0 = 1 ∧ x = e0 ∨ a0 = 1 ∧ x = -e0) ∨ (a1 = 1 ∧ x = e1 ∨ a1 = 1 ∧ x = -e1) ∨
      (a2 = 1 ∧ x = e2 ∨ a2 = 1 ∧ x = -e2) := by
  have hle : ((x 0 : ℝ)) ^ 2 + (x 1 : ℝ) ^ 2 + (x 2 : ℝ) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (x 0 : ℝ), sq_nonneg (x 1 : ℝ), sq_nonneg (x 2 : ℝ)]
  have hle' : (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 ≤ 1 := by exact_mod_cast hle
  have b0 : x 0 = -1 ∨ x 0 = 0 ∨ x 0 = 1 := by
    have : (x 0) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)]
    have : -1 ≤ x 0 ∧ x 0 ≤ 1 := by constructor <;> nlinarith
    omega
  have b1 : x 1 = -1 ∨ x 1 = 0 ∨ x 1 = 1 := by
    have : (x 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 2)]
    have : -1 ≤ x 1 ∧ x 1 ≤ 1 := by constructor <;> nlinarith
    omega
  have b2 : x 2 = -1 ∨ x 2 = 0 ∨ x 2 = 1 := by
    have : (x 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have : -1 ≤ x 2 ∧ x 2 ≤ 1 := by constructor <;> nlinarith
    omega
  have hx' : ¬ (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0) := fun ⟨a, b, c⟩ =>
    hx (by funext i; fin_cases i <;> simp [a, b, c])
  rcases b0 with h0' | h0' | h0' <;> rcases b1 with h1' | h1' | h1' <;> rcases b2 with h2' | h2' | h2' <;>
    simp [h0', h1', h2', eq_e0_iff, eq_neg_e0_iff, eq_e1_iff, eq_neg_e1_iff, eq_e2_iff,
      eq_neg_e2_iff] at hx' hle' hq ⊢
  all_goals exact hq

/-- The three coordinate vectors. -/
def eV : Fin 3 → Vec := ![e0, e1, e2]

theorem eV_ne_zero (i : Fin 3) : eV i ≠ 0 := by
  fin_cases i <;> simp [eV, e0, e1, e2, funext_iff, Fin.forall_fin_succ]

theorem ge_one_diag (C : Cell) {p : PDMat} (hp : p ∈ reach C) (hd : IsDiagMat p.1) (i : Fin 3) :
    1 ≤ p.1 i i := by
  have := reach_ge_one C hp (eV_ne_zero i)
  rw [qfR_diag _ hd] at this
  fin_cases i <;> simpa [eV, e0, e1, e2] using this

/-- **The diagonal flat meets the retract only at the identity form, and only inside the standard
top cell**: a point of the reach of a cell which is a diagonal form forces the cell to be `T₀`
and the form to be the identity. -/
theorem flat_reach (C : Cell) {p : PDMat} (hp : p ∈ reach C) (hd : IsDiagMat p.1) :
    C = T0 ∧ p.1 = 1 := by
  have key : ∀ ℓ ∈ C.val, ∃ i : Fin 3, p.1 i i = 1 ∧ ℓ = Line.mk (eV i) := by
    intro ℓ hℓ
    induction ℓ using Line.ind with
    | h x =>
      have hq := qfR_eq_one_of_reach C hp hℓ
      have hx : x ≠ 0 := by
        rintro rfl
        simp [qfR] at hq
      rw [qfR_diag _ hd] at hq
      have h0 := ge_one_diag C hp hd 0
      have h1 := ge_one_diag C hp hd 1
      have h2 := ge_one_diag C hp hd 2
      rcases diag_minimal _ _ _ h0 h1 h2 x hx hq with (⟨h, rfl⟩ | ⟨h, rfl⟩) | (⟨h, rfl⟩ | ⟨h, rfl⟩) |
          (⟨h, rfl⟩ | ⟨h, rfl⟩)
      · exact ⟨0, h, rfl⟩
      · exact ⟨0, h, by simp [eV, Line.mk_neg]⟩
      · exact ⟨1, h, rfl⟩
      · exact ⟨1, h, by simp [eV, Line.mk_neg]⟩
      · exact ⟨2, h, rfl⟩
      · exact ⟨2, h, by simp [eV, Line.mk_neg]⟩
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := C.isCell.1
  obtain ⟨ia, hia, rfl⟩ := key a ha
  obtain ⟨ib, hib, rfl⟩ := key b hb
  obtain ⟨ic, hic, rfl⟩ := key c hc
  have hab := habc.ne12
  have hbc := habc.ne23
  have hac := habc.ne13
  have hinj : Function.Injective ![ia, ib, ic] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    all_goals (exfalso; subst hij; contradiction)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  have hcover : ∀ i : Fin 3, Line.mk (eV i) ∈ C.val := by
    intro i
    obtain ⟨k, hk⟩ := hsurj i
    fin_cases k
    · simp at hk; rw [← hk]; exact ha
    · simp at hk; rw [← hk]; exact hb
    · simp at hk; rw [← hk]; exact hc
  have hone : ∀ i : Fin 3, p.1 i i = 1 := by
    intro i
    obtain ⟨k, hk⟩ := hsurj i
    fin_cases k
    · simp at hk; rw [← hk]; exact hia
    · simp at hk; rw [← hk]; exact hib
    · simp at hk; rw [← hk]; exact hic
  refine ⟨Cell.ext ?_, ?_⟩
  · ext ℓ
    constructor
    · intro hℓ
      obtain ⟨i, -, rfl⟩ := key ℓ hℓ
      fin_cases i <;> simp [T0, T0set, eV]
    · intro hℓ
      simp only [T0, T0set, Finset.mem_insert, Finset.mem_singleton] at hℓ
      rcases hℓ with rfl | rfl | rfl
      · exact hcover 0
      · exact hcover 1
      · exact hcover 2
  · ext i j
    by_cases hij : i = j
    · subst hij; simpa using hone i
    · rw [hd i j hij]; simp [hij]

end TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry
