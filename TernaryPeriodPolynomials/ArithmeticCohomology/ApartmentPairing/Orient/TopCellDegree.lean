module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.FanData

@[expose] public section


/-!
# The local degree of the standard top cell: `dT0 = - lamPos`

The cone chain `Phi3 = coneData.phi 3 T₀` of the standard top cell of the well-rounded retract is a
signed sum of ninety-six flag simplices `(b(T₀), b(F₂), b(F₁), b(F₀))` (`Phi3_shape`, `chain_flag`:
`F₂ = T₀ ∪ {i}`, `F₁ = T₀ ∪ {i,j}`, `F₀` a vertex).  Combining the finite checks of `FanData` with the
fan theorem (`fan_degree`):

* `Phi3_bdry_bound`: the outer triangles stay at distance `≥ 1/3` from the identity (in the
  linearized coordinates `Lc`);
* `Phi3_out`: the point `Pq = (1/30, -1/120, 1/20)` lies in no flag simplex except `y0z`, the flag
  `(k,i,j) = (0,9,11)` (`edgeDet_y0z > 0`, `sigma0_point`);
* `Phi3_y0z : Phi3 y0z = -1`: the coefficient of that flag, computed from the library's own
  insertion signs `insSignQ` (`sign2 = -1`, `sign1 = 1`, `sign0 = -1`) and the orientation
  `epsQ D0z = -1` (a `6 × 6` determinant over `𝔽₃`);
* **`dT0_eq_neg_lamPos : dT0 = -lamPos`**: the local degree of the standard top cell is minus the
  universal local class of a positively oriented tetrahedron around the origin.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical
open TernaryPoly TernaryPoly.SymmetricSpacePositive Finsupp
  TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry
  TernaryPeriodPolynomials.FreeResolution

namespace TernaryPeriodPolynomials.Argument.Lemma33.Orient

/-! ### Shapes of the simplices of the cone recursion -/

theorem phi_succ_shape (n : ℕ) (C : Cell) (y : AffSimp PDMat (n + 1))
    (hy : y ∈ (coneData.phi (n + 1) C).support) :
    ∃ C' : Cell, incQ C C' ≠ 0 ∧ ∃ y' ∈ (coneData.phi n C').support,
      y = AffSimp.cone (bpt C) y' := by
  rw [ConeData.phi_succ] at hy
  obtain ⟨y', hy', rfl⟩ : ∃ y' ∈ (coneData.Phi n (coneData.inc C)).support,
      AffSimp.cone (coneData.bpt C) y' = y := by
    have := ConeData.support_coneAff_subset (coneData.bpt C) (coneData.Phi n (coneData.inc C)) hy
    simpa only [Finset.mem_image] using this
  obtain ⟨C', hC', hy''⟩ : ∃ C' ∈ (coneData.inc C).support, y' ∈ (coneData.phi n C').support := by
    have := coneData.support_Phi_subset n (coneData.inc C) hy'
    simpa only [Finset.mem_biUnion] using this
  exact ⟨C', Finsupp.mem_support_iff.mp hC', y', hy'', rfl⟩

theorem phi_zero_shape (C : Cell) (y : AffSimp PDMat 0) (hy : y ∈ (coneData.phi 0 C).support) :
    y = fun _ => bpt C := by
  unfold ConeData.phi at hy
  have h1 := Finsupp.support_smul hy
  rw [ptAff] at h1
  have h2 := Finsupp.support_single_subset h1
  rw [Finset.mem_singleton] at h2
  exact h2

theorem Phi3_shape (y : AffSimp PDMat 3) (hy : y ∈ Phi3.support) :
    ∃ D2 D1 D0 : Cell, incQ T0 D2 ≠ 0 ∧ incQ D2 D1 ≠ 0 ∧ incQ D1 D0 ≠ 0 ∧
      y = ![bpt T0, bpt D2, bpt D1, bpt D0] := by
  obtain ⟨D2, h2, y2, hy2, rfl⟩ := phi_succ_shape 2 T0 y hy
  obtain ⟨D1, h1, y1, hy1, rfl⟩ := phi_succ_shape 1 D2 y2 hy2
  obtain ⟨D0, h0, y0, hy0, rfl⟩ := phi_succ_shape 0 D1 y1 hy1
  have := phi_zero_shape D0 y0 hy0
  subst this
  refine ⟨D2, D1, D0, h2, h1, h0, ?_⟩
  funext k
  fin_cases k <;> rfl

theorem bdry_shape (y : AffSimp PDMat 2) (hy : y ∈ (dAff PDMat 2 Phi3).support) :
    ∃ D2 D1 D0 : Cell, incQ T0 D2 ≠ 0 ∧ incQ D2 D1 ≠ 0 ∧ incQ D1 D0 ≠ 0 ∧
      y = ![bpt D2, bpt D1, bpt D0] := by
  have hb : dAff PDMat 2 Phi3 = coneData.Phi 2 (incQ T0) := coneData.phi_boundary 2 T0 T0_grade
  rw [hb] at hy
  obtain ⟨D2, hD2, hy2⟩ : ∃ D ∈ (incQ T0).support, y ∈ (coneData.phi 2 D).support := by
    have := coneData.support_Phi_subset 2 (incQ T0) hy
    simpa only [Finset.mem_biUnion] using this
  obtain ⟨D1, h1, y1, hy1, rfl⟩ := phi_succ_shape 1 D2 y hy2
  obtain ⟨D0, h0, y0, hy0, rfl⟩ := phi_succ_shape 0 D1 y1 hy1
  have := phi_zero_shape D0 y0 hy0
  subst this
  refine ⟨D2, D1, D0, Finsupp.mem_support_iff.mp hD2, h1, h0, ?_⟩
  funext k
  fin_cases k <;> rfl

/-! ### Chains of faces of the standard top cell -/

theorem three_le_of_not_mem : ∀ i : Fin 13, i ∉ ({0, 1, 2} : Finset (Fin 13)) → 3 ≤ i.val := by
  decide

theorem card_Ix (D : Cell) (h : T0.val ⊆ D.val) : (Ix D).card = D.val.card := by
  obtain ⟨hD, -⟩ := cell_above D h
  conv_rhs => rw [hD]
  rw [Finset.card_image_of_injective _ lineOf_injective]

theorem Ix_mono {D D' : Cell} (h : D.val ⊆ D'.val) : Ix D ⊆ Ix D' :=
  fun _ hi => (mem_Ix _ _).mpr (h ((mem_Ix _ _).mp hi))

theorem incQ_support (C D : Cell) (h : incQ C D ≠ 0) :
    ∃ w ∈ nbrs C.val, D.val = insert w C.val := by
  have hD : D.val ∈ (coboundaryOfQ C.val).support := by
    rw [Finsupp.mem_support_iff]
    exact h
  obtain ⟨w, hw, hwD⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hD)
  have hS' := Finsupp.support_smul hwD
  have := Finsupp.support_single_subset hS'
  rw [Finset.mem_singleton] at this
  exact ⟨w, hw, this⟩

/-- **One step down in the face poset of the standard top cell**: a boundary cell of a cell above `T₀`
adds exactly one line, and is again a face of a vertex. -/
theorem face_step (C D : Cell) (hC : T0.val ⊆ C.val) (h : incQ C D ≠ 0) :
    T0.val ⊆ D.val ∧ ∃ i, i ∉ Ix C ∧ Ix D = insert i (Ix C) ∧ ∃ k, Ix D ⊆ Mk k := by
  have hCD := subset_of_incQ_ne_zero C D h
  have hD := hC.trans hCD
  obtain ⟨w, hw, hwD⟩ := incQ_support C D h
  obtain ⟨hDe, k, hk⟩ := cell_above D hD
  have hwmem : w ∈ D.val := by rw [hwD]; exact Finset.mem_insert_self _ _
  rw [hDe] at hwmem
  obtain ⟨i, hiD, rfl⟩ := Finset.mem_image.mp hwmem
  have hiC : i ∉ Ix C := fun hi => ((mem_nbrs C.isCell.1 _).mp hw).1 ((mem_Ix _ _).mp hi)
  refine ⟨hD, i, hiC, ?_, k, hk⟩
  ext j
  have e1 : j ∈ Ix D ↔ lineOf j ∈ insert (lineOf i) C.val := by rw [mem_Ix, hwD]
  rw [e1, Finset.mem_insert, Finset.mem_insert]
  constructor
  · rintro (h' | h')
    · exact Or.inl (lineOf_injective h')
    · exact Or.inr ((mem_Ix C j).mpr h')
  · rintro (h' | h')
    · exact Or.inl (h' ▸ rfl)
    · exact Or.inr ((mem_Ix C j).mp h')

theorem chain_flag (D2 D1 D0 : Cell) (h2 : incQ T0 D2 ≠ 0) (h1 : incQ D2 D1 ≠ 0)
    (h0 : incQ D1 D0 ≠ 0) :
    ∃ k i j, valid k i j ∧ Ix D2 = X2 i ∧ Ix D1 = X1 i j ∧ Ix D0 = Mk k := by
  obtain ⟨t2, i, hi, hX2, -⟩ := face_step T0 D2 (subset_refl _) h2
  obtain ⟨t1, j, hj, hX1, -⟩ := face_step D2 D1 t2 h1
  obtain ⟨t0, l, hl, hX0, k, hk⟩ := face_step D1 D0 t1 h0
  rw [Ix_T0] at hX2 hi
  have hX2' : Ix D2 = X2 i := hX2
  have hX1' : Ix D1 = X1 i j := by rw [hX1, hX2']; rfl
  have hiX : i ∈ X2 i := Finset.mem_insert_self _ _
  have hjX : j ∈ X1 i j := Finset.mem_insert_self _ _
  have hjn : j ∉ X2 i := by rw [← hX2']; exact hj
  have hln : l ∉ X1 i j := by rw [← hX1']; exact hl
  have hc : (Ix D0).card = 6 := by
    have hc2 : (X2 i).card = 4 := by
      unfold X2; rw [Finset.card_insert_of_notMem hi]; decide
    have hc1 : (X1 i j).card = 5 := by
      unfold X1; rw [Finset.card_insert_of_notMem hjn, hc2]
    rw [hX0, hX1', Finset.card_insert_of_notMem hln, hc1]
  have i0 : Ix D0 = Mk k := by
    apply Finset.eq_of_subset_of_card_le hk
    rw [Mk_card, hc]
  have m21 := Ix_mono (subset_of_incQ_ne_zero _ _ h1)
  have m10 := Ix_mono (subset_of_incQ_ne_zero _ _ h0)
  refine ⟨k, i, j, ⟨?_, ?_, three_le_of_not_mem i hi, ?_, ?_⟩, hX2', hX1', i0⟩
  · rw [← i0]; exact m10 (m21 (hX2' ▸ hiX))
  · rw [← i0]; exact m10 (hX1' ▸ hjX)
  · apply three_le_of_not_mem
    intro h
    exact hjn (by unfold X2; exact Finset.mem_insert_of_mem h)
  · intro hij
    exact hjn (hij ▸ hiX)


/-! ### Linearized vertices of a flag -/

theorem Lc_bpt_T0 : Lc (bpt T0) = 0 := by
  change Lraw (bptMat T0) = 0
  rw [bptMat_T0]
  ext c
  fin_cases c <;> simp [Lraw]

theorem ofQ_zero : ofQ (fun _ => 0) = 0 := by
  ext c; simp [ofQ]

theorem wy_flag (D2 D1 D0 : Cell) (h2 : incQ T0 D2 ≠ 0) (h1 : incQ D2 D1 ≠ 0) (h0 : incQ D1 D0 ≠ 0)
    (k : Fin 16) (i j : Fin 13) (e2 : Ix D2 = X2 i) (e1 : Ix D1 = X1 i j) (e0 : Ix D0 = Mk k) :
    wy ![bpt T0, bpt D2, bpt D1, bpt D0] = fun m => ofQ (vq k i j m) := by
  have a2 := subset_of_incQ_ne_zero _ _ h2
  have a1 := a2.trans (subset_of_incQ_ne_zero _ _ h1)
  have a0 := a1.trans (subset_of_incQ_ne_zero _ _ h0)
  funext m
  fin_cases m
  · simp only [wy]
    change Lc (bpt T0) = ofQ (fun _ => 0)
    rw [Lc_bpt_T0, ofQ_zero]
  · simp only [wy]
    change Lc (bpt D2) = ofQ (bLq (X2 i))
    rw [Lc_bpt D2 a2, e2]
  · simp only [wy]
    change Lc (bpt D1) = ofQ (bLq (X1 i j))
    rw [Lc_bpt D1 a1, e1]
  · simp only [wy]
    change Lc (bpt D0) = ofQ (bLq (Mk k))
    rw [Lc_bpt D0 a0, e0]


/-! ### Soundness of the finite checks -/

theorem affEMap_ofQ_apply (v : Fin 4 → Fin 3 → ℚ) (t : Dl) (c : Fin 3) :
    affEMap (fun m => ofQ (v m)) t c = ∑ m, t.weights m * (v m c : ℝ) := by
  simp [affEMap, ofQ, Finset.sum_apply]

theorem outside_sound (v : Fin 4 → Fin 3 → ℚ) (h0 : v 0 = fun _ => 0) (p : Fin 3 → ℚ)
    (h : outsideQ (v 1) (v 2) (v 3) p) (t : Dl) : affEMap (fun m => ofQ (v m)) t ≠ ofQ p := by
  intro heq
  have hc : ∀ c, (p c : ℝ) = t.weights 1 * (v 1 c : ℝ) + t.weights 2 * (v 2 c : ℝ) +
      t.weights 3 * (v 3 c : ℝ) := by
    intro c
    have := congrArg (fun x : E3 => x c) heq
    simp only at this
    rw [affEMap_ofQ_apply] at this
    have hp : (ofQ p) c = (p c : ℝ) := rfl
    rw [hp, Fin.sum_univ_four, h0] at this
    simp at this
    linarith
  have hn : ∀ m, 0 ≤ t.weights m := t.weights_nonneg
  have hs : t.weights 0 + t.weights 1 + t.weights 2 + t.weights 3 = 1 := by
    have h4 : ∑ k, t.weights k = 1 := t.total_of_fintype
    rw [Fin.sum_univ_four] at h4
    exact h4
  have n0 := hn 0
  have n1 := hn 1
  have n2 := hn 2
  have n3 := hn 3
  have e1 : ((det3q p (v 2) (v 3) : ℚ) : ℝ) = t.weights 1 * ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) := by
    unfold det3q; push_cast; rw [hc 0, hc 1, hc 2]; ring
  have e2 : ((det3q (v 1) p (v 3) : ℚ) : ℝ) = t.weights 2 * ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) := by
    unfold det3q; push_cast; rw [hc 0, hc 1, hc 2]; ring
  have e3 : ((det3q (v 1) (v 2) p : ℚ) : ℝ) = t.weights 3 * ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) := by
    unfold det3q; push_cast; rw [hc 0, hc 1, hc 2]; ring
  rcases h with ⟨hD, h | h | h | h⟩ | ⟨hD, h | h | h | h⟩
  · have hD' : (0 : ℝ) < ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) := by exact_mod_cast hD
    have h' : ((det3q p (v 2) (v 3) : ℚ) : ℝ) < 0 := by exact_mod_cast h
    rw [e1] at h'; nlinarith
  · have hD' : (0 : ℝ) < ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) := by exact_mod_cast hD
    have h' : ((det3q (v 1) p (v 3) : ℚ) : ℝ) < 0 := by exact_mod_cast h
    rw [e2] at h'; nlinarith
  · have hD' : (0 : ℝ) < ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) := by exact_mod_cast hD
    have h' : ((det3q (v 1) (v 2) p : ℚ) : ℝ) < 0 := by exact_mod_cast h
    rw [e3] at h'; nlinarith
  · have hD' : (0 : ℝ) < ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) := by exact_mod_cast hD
    have h' : ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) < ((det3q p (v 2) (v 3) : ℚ) : ℝ) +
        ((det3q (v 1) p (v 3) : ℚ) : ℝ) + ((det3q (v 1) (v 2) p : ℚ) : ℝ) := by exact_mod_cast h
    rw [e1, e2, e3] at h'; nlinarith
  · have hD' : ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) < 0 := by exact_mod_cast hD
    have h' : (0 : ℝ) < ((det3q p (v 2) (v 3) : ℚ) : ℝ) := by exact_mod_cast h
    rw [e1] at h'; nlinarith
  · have hD' : ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) < 0 := by exact_mod_cast hD
    have h' : (0 : ℝ) < ((det3q (v 1) p (v 3) : ℚ) : ℝ) := by exact_mod_cast h
    rw [e2] at h'; nlinarith
  · have hD' : ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) < 0 := by exact_mod_cast hD
    have h' : (0 : ℝ) < ((det3q (v 1) (v 2) p : ℚ) : ℝ) := by exact_mod_cast h
    rw [e3] at h'; nlinarith
  · have hD' : ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) < 0 := by exact_mod_cast hD
    have h' : ((det3q p (v 2) (v 3) : ℚ) : ℝ) + ((det3q (v 1) p (v 3) : ℚ) : ℝ) +
        ((det3q (v 1) (v 2) p : ℚ) : ℝ) < ((det3q (v 1) (v 2) (v 3) : ℚ) : ℝ) := by exact_mod_cast h
    rw [e1, e2, e3] at h'; nlinarith


theorem tri_norm_bound (v : Fin 3 → Fin 3 → ℚ) (hT : triOK (v 0) (v 1) (v 2)) (t : Convexity.StdSimplex ℝ (Fin 3)) :
    1 / 3 ≤ ‖∑ m, t.weights m • ofQ (v m)‖ := by
  set x : E3 := ∑ m, t.weights m • ofQ (v m) with hx
  have hxc : ∀ c, x c = ∑ m, t.weights m * (v m c : ℝ) := by
    intro c; simp [hx, ofQ, Finset.sum_apply]
  have hs : ∑ m, t.weights m = 1 := t.total_of_fintype
  rw [Fin.sum_univ_three] at hs
  set n := crossq (v 1 - v 0) (v 2 - v 0) with hn
  have key : (n 0 : ℝ) * x 0 + (n 1 : ℝ) * x 1 + (n 2 : ℝ) * x 2 =
      (det3q (v 0) (v 1) (v 2) : ℝ) := by
    rw [hxc, hxc, hxc]
    simp only [hn, crossq, det3q, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_three]
    push_cast
    linear_combination (((v 0 0 : ℚ) : ℝ) * (((v 1 1 : ℚ) : ℝ) * ((v 2 2 : ℚ) : ℝ) -
      ((v 1 2 : ℚ) : ℝ) * ((v 2 1 : ℚ) : ℝ)) - ((v 0 1 : ℚ) : ℝ) * (((v 1 0 : ℚ) : ℝ) *
      ((v 2 2 : ℚ) : ℝ) - ((v 1 2 : ℚ) : ℝ) * ((v 2 0 : ℚ) : ℝ)) + ((v 0 2 : ℚ) : ℝ) *
      (((v 1 0 : ℚ) : ℝ) * ((v 2 1 : ℚ) : ℝ) - ((v 1 1 : ℚ) : ℝ) * ((v 2 0 : ℚ) : ℝ))) * hs
  have hxn : ∀ c, |x c| ≤ ‖x‖ := fun c => by
    have := PiLp.norm_apply_le x c
    rwa [Real.norm_eq_abs] at this
  obtain ⟨hl, hle⟩ := hT
  have hl' : (0 : ℝ) < |(n 0 : ℝ)| + |(n 1 : ℝ)| + |(n 2 : ℝ)| := by
    have : (0 : ℝ) < ((l1q n : ℚ) : ℝ) := by exact_mod_cast hl
    simpa [l1q] using this
  have hle' : |(n 0 : ℝ)| + |(n 1 : ℝ)| + |(n 2 : ℝ)| ≤ 3 * |(det3q (v 0) (v 1) (v 2) : ℝ)| := by
    have : ((l1q n : ℚ) : ℝ) ≤ 3 * ((|det3q (v 0) (v 1) (v 2)| : ℚ) : ℝ) := by exact_mod_cast hle
    simpa [l1q] using this
  have h1 : |(det3q (v 0) (v 1) (v 2) : ℝ)| ≤ (|(n 0 : ℝ)| + |(n 1 : ℝ)| + |(n 2 : ℝ)|) * ‖x‖ := by
    rw [← key]
    calc |(n 0 : ℝ) * x 0 + (n 1 : ℝ) * x 1 + (n 2 : ℝ) * x 2|
        ≤ |(n 0 : ℝ) * x 0| + |(n 1 : ℝ) * x 1| + |(n 2 : ℝ) * x 2| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ = |(n 0 : ℝ)| * |x 0| + |(n 1 : ℝ)| * |x 1| + |(n 2 : ℝ)| * |x 2| := by
          simp only [abs_mul]
      _ ≤ |(n 0 : ℝ)| * ‖x‖ + |(n 1 : ℝ)| * ‖x‖ + |(n 2 : ℝ)| * ‖x‖ := by
          gcongr <;> exact hxn _
      _ = _ := by ring
  nlinarith [norm_nonneg x]


/-! ### The chosen flag -/

/-- The cell with the given index set. -/
def cellOfIx (X : Finset (Fin 13)) (hT : ({0, 1, 2} : Finset (Fin 13)) ⊆ X) (k : Fin 16)
    (hk : X ⊆ Mk k) : Cell :=
  ⟨X.image lineOf, T0.isCell.1.mono (by rw [T0_val]; exact Finset.image_subset_image hT),
    ⟨vtx16 k, by rw [vtx16_M]; exact Finset.image_subset_image hk⟩⟩

theorem cellOfIx_val (X : Finset (Fin 13)) (hT : ({0, 1, 2} : Finset (Fin 13)) ⊆ X) (k : Fin 16)
    (hk : X ⊆ Mk k) : (cellOfIx X hT k hk).val = X.image lineOf := rfl

theorem above_cellOfIx (X : Finset (Fin 13)) (hT : ({0, 1, 2} : Finset (Fin 13)) ⊆ X) (k : Fin 16)
    (hk : X ⊆ Mk k) : T0.val ⊆ (cellOfIx X hT k hk).val := by
  rw [T0_val, cellOfIx_val]; exact Finset.image_subset_image hT

theorem Ix_cellOfIx (X : Finset (Fin 13)) (hT : ({0, 1, 2} : Finset (Fin 13)) ⊆ X) (k : Fin 16)
    (hk : X ⊆ Mk k) : Ix (cellOfIx X hT k hk) = X := by
  ext i
  rw [mem_Ix, cellOfIx_val]
  constructor
  · intro h
    obtain ⟨j, hj, e⟩ := Finset.mem_image.mp h
    rw [← lineOf_injective e]; exact hj
  · intro h; exact Finset.mem_image.mpr ⟨i, h, rfl⟩

theorem cell_ext_of_Ix {D D' : Cell} (hD : T0.val ⊆ D.val) (hD' : T0.val ⊆ D'.val)
    (h : Ix D = Ix D') : D = D' :=
  Cell.ext (by rw [(cell_above D hD).1, (cell_above D' hD').1, h])

/-- The chosen facet, edge and vertex of the standard top cell. -/
def D2z : Cell := cellOfIx (X2 9) (by decide) 0 (by decide)
def D1z : Cell := cellOfIx (X1 9 11) (by decide) 0 (by decide)
def D0z : Cell := cellOfIx (Mk 0) (Mk_base 0) 0 (subset_refl _)

/-- The chosen flag simplex. -/
def y0z : AffSimp PDMat 3 := ![bpt T0, bpt D2z, bpt D1z, bpt D0z]

theorem above_D2z : T0.val ⊆ D2z.val := above_cellOfIx _ _ _ _
theorem above_D1z : T0.val ⊆ D1z.val := above_cellOfIx _ _ _ _
theorem above_D0z : T0.val ⊆ D0z.val := above_cellOfIx _ _ _ _
theorem Ix_D2z : Ix D2z = X2 9 := Ix_cellOfIx _ _ _ _
theorem Ix_D1z : Ix D1z = X1 9 11 := Ix_cellOfIx _ _ _ _
theorem Ix_D0z : Ix D0z = Mk 0 := Ix_cellOfIx _ _ _ _

theorem incQ_of_insert (C D : Cell) (w : Line) (hw : w ∈ nbrs C.val)
    (hD : D.val = insert w C.val) : incQ C D = insSignQ C.val w := by
  rw [incQ_apply, coboundaryOfQ, Finsupp.finsetSum_apply, Finset.sum_eq_single w]
  · rw [Finsupp.smul_apply, hD, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro w' hw' hne
    rw [Finsupp.smul_apply, hD, Finsupp.single_apply]
    have hne' : insert w' C.val ≠ insert w C.val := by
      intro h
      have hw'C : w' ∉ C.val := ((mem_nbrs C.isCell.1 w').mp hw').1
      have : w' ∈ insert w C.val := h ▸ Finset.mem_insert_self w' C.val
      rcases Finset.mem_insert.mp this with h' | h'
      · exact hne h'
      · exact hw'C h'
    simp [hne']
  · intro hn; exact absurd hw hn

theorem lineOf_mem_nbrs (C : Cell) (hC : T0.val ⊆ C.val) (j : Fin 13) (k : Fin 16) (hj : j ∉ Ix C)
    (hk : insert j (Ix C) ⊆ Mk k) : lineOf j ∈ nbrs C.val := by
  rw [mem_nbrs C.isCell.1]
  refine ⟨fun h => hj ((mem_Ix _ _).mpr h), vtx16 k, ?_⟩
  rw [vtx16_M, (cell_above C hC).1, ← Finset.image_insert]
  exact Finset.image_subset_image hk

theorem insert_image_lineOf (j : Fin 13) (X : Finset (Fin 13)) :
    (insert j X).image lineOf = insert (lineOf j) (X.image lineOf) := Finset.image_insert _ _ _

theorem inc2 : incQ T0 D2z = insSignQ T0.val (lineOf 9) := by
  apply incQ_of_insert
  · apply lineOf_mem_nbrs T0 (subset_refl _) 9 0
    · rw [Ix_T0]; decide
    · rw [Ix_T0]; decide
  · rw [D2z, cellOfIx_val, X2, insert_image_lineOf, T0_val]

theorem inc1 : incQ D2z D1z = insSignQ D2z.val (lineOf 11) := by
  apply incQ_of_insert
  · apply lineOf_mem_nbrs D2z above_D2z 11 0
    · rw [Ix_D2z]; decide
    · rw [Ix_D2z]; decide
  · rw [D1z, cellOfIx_val, X1, insert_image_lineOf]; rfl

theorem inc0 : incQ D1z D0z = insSignQ D1z.val (lineOf 12) := by
  apply incQ_of_insert
  · apply lineOf_mem_nbrs D1z above_D1z 12 0
    · rw [Ix_D1z]; decide
    · rw [Ix_D1z]; decide
  · have : Mk 0 = insert 12 (X1 9 11) := by decide
    rw [D0z, cellOfIx_val, this, insert_image_lineOf]; rfl


/-! ### Signs and orientations -/

/-- The label of the `i`-th line. -/
def lab13 (i : Fin 13) : ℕ := labelVec (lineV i)

theorem insSignQ_ix (C : Cell) (hC : T0.val ⊆ C.val) (j : Fin 13) :
    insSignQ C.val (lineOf j) =
      (-1) ^ (((Ix C).image lab13).filter (· < lab13 j)).card := by
  unfold insSignQ
  rw [(cell_above C hC).1, Finset.image_image]
  rfl

theorem sign2 : incQ T0 D2z = -1 := by
  rw [inc2, insSignQ_ix _ (subset_refl _), Ix_T0]
  have : ((({0, 1, 2} : Finset (Fin 13)).image lab13).filter (· < lab13 9)).card = 3 := by decide
  rw [this]; norm_num

theorem sign1 : incQ D2z D1z = 1 := by
  rw [inc1, insSignQ_ix _ above_D2z, Ix_D2z]
  have : (((X2 9).image lab13).filter (· < lab13 11)).card = 2 := by decide
  rw [this]; norm_num

theorem sign0 : incQ D1z D0z = -1 := by
  rw [inc0, insSignQ_ix _ above_D1z, Ix_D1z]
  have : (((X1 9 11).image lab13).filter (· < lab13 12)).card = 5 := by decide
  rw [this]; norm_num

theorem card_D0z : D0z.val.card = 6 := by
  rw [← card_Ix D0z above_D0z, Ix_D0z, Mk_card]

theorem labelSet_D0z : D0z.val.image Line.label = ({1, 3, 4, 9, 10, 13} : Finset ℕ) := by
  rw [D0z, cellOfIx_val, Finset.image_image]
  have : (Mk 0).image (Line.label ∘ lineOf) = (Mk 0).image lab13 := rfl
  rw [this]
  decide

theorem epsMod_D0z : epsMod D0z.val = -1 := by
  unfold epsMod labelDet
  rw [labelSet_D0z]
  have hc : ({1, 3, 4, 9, 10, 13} : Finset ℕ).card = 6 := by decide
  rw [dite_eq_left hc]
  have he : ∀ i, ({1, 3, 4, 9, 10, 13} : Finset ℕ).orderEmbOfFin hc i = ![1, 3, 4, 9, 10, 13] i := by
    intro i
    refine (congrFun (Finset.orderEmbOfFin_unique hc (f := ![1, 3, 4, 9, 10, 13]) ?_ ?_) i).symm
    · intro x; fin_cases x <;> decide
    · intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all
  have hs : sortedRows labelRow ({1, 3, 4, 9, 10, 13} : Finset ℕ) hc =
      fun i => labelRow (![1, 3, 4, 9, 10, 13] i) := by
    funext i
    unfold sortedRows
    rw [he]
  rw [hs]
  decide +kernel

theorem eps_D0z : epsQ D0z = -1 := by
  unfold epsQ
  rw [ite_eq_left card_D0z, epsMod_D0z]
  decide


/-! ### The coefficient of the chosen flag -/

theorem cone_injective (b : PDMat) {n : ℕ} :
    Function.Injective (AffSimp.cone b : AffSimp PDMat n → AffSimp PDMat (n + 1)) := by
  intro y1 y2 h
  funext k
  have := congrFun h k.succ
  simpa [AffSimp.cone] using this

theorem coneAff_apply_cone (b : PDMat) {n : ℕ} (c : AffChain PDMat n) (y' : AffSimp PDMat n) :
    coneAff b n c (AffSimp.cone b y') = c y' := by
  unfold coneAff
  rw [Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_apply_of_injective (cone_injective b) c y'

theorem Phi_apply (n : ℕ) (z : Cell →₀ ℚ) (y' : AffSimp PDMat n) :
    (coneData.Phi n z) y' = ∑ C ∈ z.support, z C * (coneData.phi n C) y' := by
  unfold ConeData.Phi
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  simp [Finsupp.smul_apply]

theorem phi_head (n : ℕ) (C : Cell) (y' : AffSimp PDMat n) (hy : y' ∈ (coneData.phi n C).support) :
    y' 0 = bpt C := by
  cases n with
  | zero => rw [phi_zero_shape C y' hy]
  | succ n =>
    obtain ⟨C', -, y'', -, rfl⟩ := phi_succ_shape n C y' hy
    rfl

theorem phi_peel (n : ℕ) (C D0 : Cell) (hD0 : incQ C D0 ≠ 0)
    (huniq : ∀ D, incQ C D ≠ 0 → bpt D = bpt D0 → D = D0) (y1 : AffSimp PDMat n)
    (hy1 : y1 0 = bpt D0) :
    (coneData.phi (n + 1) C) (AffSimp.cone (bpt C) y1) = incQ C D0 * (coneData.phi n D0) y1 := by
  rw [ConeData.phi_succ]
  change (coneAff (bpt C) n (coneData.Phi n (incQ C))) (AffSimp.cone (bpt C) y1) = _
  rw [coneAff_apply_cone, Phi_apply, Finset.sum_eq_single D0]
  · intro D hD hne
    by_cases hz : (coneData.phi n D) y1 = 0
    · rw [hz, mul_zero]
    · exfalso
      have := phi_head n D y1 (Finsupp.mem_support_iff.mpr hz)
      exact hne (huniq D (Finsupp.mem_support_iff.mp hD) (this.symm.trans hy1))
  · intro hn; exact absurd (Finsupp.mem_support_iff.mpr hD0) hn

theorem ofQ_injective : Function.Injective ofQ := by
  intro v w h
  funext c
  have h1 := congrArg (fun x : E3 => x c) h
  have h2 : (v c : ℝ) = (w c : ℝ) := h1
  exact_mod_cast h2

theorem bLq_eq_of_bpt (D D' : Cell) (h : T0.val ⊆ D.val) (h' : T0.val ⊆ D'.val)
    (e : bpt D = bpt D') : bLq (Ix D) = bLq (Ix D') :=
  ofQ_injective (by rw [← Lc_bpt D h, ← Lc_bpt D' h', e])

theorem U1 (D : Cell) (hD : incQ T0 D ≠ 0) (e : bpt D = bpt D2z) : D = D2z := by
  obtain ⟨t, i, hi, hX, k, hk⟩ := face_step T0 D (subset_refl _) hD
  rw [Ix_T0] at hX hi
  have hb := bLq_eq_of_bpt D D2z t above_D2z e
  rw [hX, Ix_D2z] at hb
  have hik : i ∈ Mk k := hk (by rw [hX]; exact Finset.mem_insert_self _ _)
  have i9 : i = 9 := bLq_X2_inj i (three_le_of_not_mem i hi) ⟨k, hik⟩ hb
  apply cell_ext_of_Ix t above_D2z
  rw [hX, Ix_D2z, i9]
  rfl

theorem U2 (D : Cell) (hD : incQ D2z D ≠ 0) (e : bpt D = bpt D1z) : D = D1z := by
  obtain ⟨t, j, hj, hX, k, hk⟩ := face_step D2z D above_D2z hD
  rw [Ix_D2z] at hX hj
  have hb := bLq_eq_of_bpt D D1z t above_D1z e
  rw [hX, Ix_D1z] at hb
  have h9 : (9 : Fin 13) ∈ Mk k := hk (by rw [hX]; exact Finset.mem_insert_of_mem (by decide))
  have hjk : j ∈ Mk k := hk (by rw [hX]; exact Finset.mem_insert_self _ _)
  have h3 : 3 ≤ j.val := by
    apply three_le_of_not_mem
    intro h
    exact hj (by unfold X2; exact Finset.mem_insert_of_mem h)
  have hne : j ≠ 9 := by
    intro h
    exact hj (by rw [h]; exact Finset.mem_insert_self _ _)
  have j11 : j = 11 := bLq_X1_inj j h3 hne ⟨k, h9, hjk⟩ hb
  apply cell_ext_of_Ix t above_D1z
  rw [hX, Ix_D1z, j11]
  rfl

theorem U3 (D : Cell) (hD : incQ D1z D ≠ 0) (e : bpt D = bpt D0z) : D = D0z := by
  obtain ⟨t, l, hl, hX, k, hk⟩ := face_step D1z D above_D1z hD
  rw [Ix_D1z] at hX hl
  have hc : (Ix D).card = 6 := by
    have hc1 : (X1 9 11).card = 5 := by decide
    rw [hX, Finset.card_insert_of_notMem hl, hc1]
  have iD : Ix D = Mk k := by
    apply Finset.eq_of_subset_of_card_le hk
    rw [Mk_card, hc]
  have hb := bLq_eq_of_bpt D D0z t above_D0z e
  rw [iD, Ix_D0z] at hb
  have k0 : k = 0 := bLq_Mk_inj k hb
  apply cell_ext_of_Ix t above_D0z
  rw [iD, Ix_D0z, k0]

theorem phi_zero_apply (C : Cell) : (coneData.phi 0 C) (fun _ => bpt C) = epsQ C := by
  have h0def : coneData.phi 0 C = epsQ C • ptAff (bpt C) := rfl
  rw [h0def, Finsupp.smul_apply, ptAff, Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem Phi3_y0z : Phi3 y0z = -1 := by
  have h2 : incQ T0 D2z ≠ 0 := by rw [sign2]; norm_num
  have h1 : incQ D2z D1z ≠ 0 := by rw [sign1]; norm_num
  have h0 : incQ D1z D0z ≠ 0 := by rw [sign0]; norm_num
  have e3 : y0z = AffSimp.cone (bpt T0) ![bpt D2z, bpt D1z, bpt D0z] := by
    funext k; fin_cases k <;> rfl
  have e2 : (![bpt D2z, bpt D1z, bpt D0z] : AffSimp PDMat 2) =
      AffSimp.cone (bpt D2z) ![bpt D1z, bpt D0z] := by
    funext k; fin_cases k <;> rfl
  have e1 : (![bpt D1z, bpt D0z] : AffSimp PDMat 1) = AffSimp.cone (bpt D1z) ![bpt D0z] := by
    funext k; fin_cases k <;> rfl
  have e0 : (coneData.phi 0 D0z) ![bpt D0z] = epsQ D0z := by
    have : (![bpt D0z] : AffSimp PDMat 0) = fun _ => bpt D0z := by funext k; fin_cases k; rfl
    rw [this]
    exact phi_zero_apply D0z
  change (coneData.phi 3 T0) y0z = -1
  rw [e3, phi_peel 2 T0 D2z h2 U1 _ rfl, e2, phi_peel 1 D2z D1z h1 U2 _ rfl, e1,
    phi_peel 0 D1z D0z h0 U3 _ rfl, e0, sign2, sign1, sign0, eps_D0z]
  norm_num


/-! ### The hypotheses of the fan theorem for the standard top cell -/

theorem Phi3_bdry_bound {y : AffSimp PDMat 2} (hy : y ∈ (dAff PDMat 2 Phi3).support)
    (t : Convexity.StdSimplex ℝ (Fin (2 + 1))) : 1 / 3 ≤ ‖Lc (affMap 2 y t)‖ := by
  obtain ⟨D2, D1, D0, h2, h1, h0, rfl⟩ := bdry_shape y hy
  obtain ⟨k, i, j, hv, e2, e1, e0⟩ := chain_flag D2 D1 D0 h2 h1 h0
  have a2 := subset_of_incQ_ne_zero _ _ h2
  have a1 := a2.trans (subset_of_incQ_ne_zero _ _ h1)
  have a0 := a1.trans (subset_of_incQ_ne_zero _ _ h0)
  let v : Fin 3 → Fin 3 → ℚ := fun m => vq k i j m.succ
  have hLc : ∀ m, Lc (![bpt D2, bpt D1, bpt D0] m) = ofQ (v m) := by
    intro m
    fin_cases m
    · change Lc (bpt D2) = ofQ (bLq (X2 i)); rw [Lc_bpt D2 a2, e2]
    · change Lc (bpt D1) = ofQ (bLq (X1 i j)); rw [Lc_bpt D1 a1, e1]
    · change Lc (bpt D0) = ofQ (bLq (Mk k)); rw [Lc_bpt D0 a0, e0]
  rw [Lc_affMap]
  simp only [hLc]
  exact tri_norm_bound v (tri_all k i j hv) t

theorem Phi3_out {y : AffSimp PDMat 3} (hy : y ∈ Phi3.support) (hne : y ≠ y0z) (t : Dl) :
    affEMap (wy y) t ≠ ofQ Pq := by
  obtain ⟨D2, D1, D0, h2, h1, h0, rfl⟩ := Phi3_shape y hy
  obtain ⟨k, i, j, hv, e2, e1, e0⟩ := chain_flag D2 D1 D0 h2 h1 h0
  have a2 := subset_of_incQ_ne_zero _ _ h2
  have a1 := a2.trans (subset_of_incQ_ne_zero _ _ h1)
  have a0 := a1.trans (subset_of_incQ_ne_zero _ _ h0)
  by_cases hf : (k, i, j) = f0
  · exfalso
    apply hne
    have hk : k = 0 ∧ i = 9 ∧ j = 11 := by
      have := Prod.ext_iff.mp hf
      simpa [f0, Prod.ext_iff] using hf
    obtain ⟨rfl, rfl, rfl⟩ := hk
    have c2 : D2 = D2z := cell_ext_of_Ix a2 above_D2z (by rw [e2, Ix_D2z])
    have c1 : D1 = D1z := cell_ext_of_Ix a1 above_D1z (by rw [e1, Ix_D1z])
    have c0 : D0 = D0z := cell_ext_of_Ix a0 above_D0z (by rw [e0, Ix_D0z])
    rw [c2, c1, c0]
    rfl
  · rw [wy_flag D2 D1 D0 h2 h1 h0 k i j e2 e1 e0]
    exact outside_sound (vq k i j) rfl Pq (outside_all k i j hv hf) t

theorem incs_ne : incQ T0 D2z ≠ 0 ∧ incQ D2z D1z ≠ 0 ∧ incQ D1z D0z ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sign2]; norm_num
  · rw [sign1]; norm_num
  · rw [sign0]; norm_num

theorem wy_y0z : wy y0z = fun m => ofQ (vq 0 9 11 m) :=
  wy_flag D2z D1z D0z incs_ne.1 incs_ne.2.1 incs_ne.2.2 0 9 11 Ix_D2z Ix_D1z Ix_D0z

/-- The barycentric coordinates of the point `Pq` in the chosen flag simplex. -/
def sigma0 : Fin (3 + 1) → ℝ := ![9 / 10, 1 / 30, 1 / 30, 1 / 30]

theorem sigma0_pos : ∀ k, 0 < sigma0 k := by
  intro k; fin_cases k <;> simp [sigma0]

theorem sigma0_sum : ∑ k, sigma0 k = 1 := by
  simp [sigma0, Fin.sum_univ_four]; norm_num

theorem sigma0_point : ∑ k, sigma0 k • wy y0z k = ofQ Pq := by
  rw [wy_y0z]
  ext c
  have hP2 : Pq c = 1 / 30 * (vq 0 9 11 1 c + vq 0 9 11 2 c + vq 0 9 11 3 c) := Pq_sum c
  have hP' : (Pq c : ℝ) = 1 / 30 * ((vq 0 9 11 1 c : ℝ) + (vq 0 9 11 2 c : ℝ) + (vq 0 9 11 3 c : ℝ)) := by
    rw [hP2]; push_cast; ring
  have h0 : (vq 0 9 11 0 c : ℝ) = 0 := by simp [vq]
  simp [Fin.sum_univ_four, h0, sigma0, ofQ]
  linarith

theorem edgeDet_y0z : 0 < edgeDet (wy y0z) := by
  rw [wy_y0z]
  have hd : (0 : ℝ) < ((det3q (vq 0 9 11 1) (vq 0 9 11 2) (vq 0 9 11 3) : ℚ) : ℝ) := by
    exact_mod_cast f0_det
  have e : edgeDet (fun m => ofQ (vq 0 9 11 m)) =
      ((det3q (vq 0 9 11 1) (vq 0 9 11 2) (vq 0 9 11 3) : ℚ) : ℝ) := by
    have h0 : ∀ c, (vq 0 9 11 0 c : ℝ) = 0 := fun c => by simp [vq]
    simp only [edgeDet, Matrix.det_fin_three, Matrix.of_apply, ofQ, det3q]
    simp [h0]
    ring
  rw [e]; exact hd

theorem Pq_norm_lt : ‖ofQ Pq‖ < 1 / 3 := by
  have h := Pq_norm
  have h' : ((Pq 0 : ℚ) : ℝ) ^ 2 + ((Pq 1 : ℚ) : ℝ) ^ 2 + ((Pq 2 : ℚ) : ℝ) ^ 2 < 1 / 9 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at this
    exact this
  by_contra hc
  have hc := not_lt.mp hc
  have hsq : ‖ofQ Pq‖ ^ 2 = ((Pq 0 : ℚ) : ℝ) ^ 2 + ((Pq 1 : ℚ) : ℝ) ^ 2 + ((Pq 2 : ℚ) : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    have e : ∀ c, ‖(ofQ Pq) c‖ ^ 2 = ((Pq c : ℚ) : ℝ) ^ 2 := fun c => by
      rw [Real.norm_eq_abs, sq_abs]; rfl
    rw [e, e, e]
  nlinarith [norm_nonneg (ofQ Pq)]

/-- **The local degree of the standard top cell**: `dT0 = - lamPos`. -/
theorem dT0_eq_neg_lamPos : dT0 = -lamPos := by
  obtain ⟨h, hd⟩ := fan_degree Phi3 (1 / 3) (fun y hy t => Phi3_bdry_bound hy t) (ofQ Pq)
    Pq_norm_lt y0z (fun y hy hne t => Phi3_out hy hne t) sigma0 sigma0_pos sigma0_sum
    sigma0_point edgeDet_y0z
  rw [dT0_eq_degRel_lin, degRel_congr _ _ lin_relCycle h rfl, hd, Phi3_y0z]
  ring

section Calibration

open CategoryTheory TernaryPoly.RationalSphere TernaryPoly.EuclideanLocalHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalSingularAugmentation
  TernaryPoly.ContractibleSingularHomology

theorem dT0_ne_zero_iff : dT0 ≠ 0 ↔ lamPos ≠ 0 := by
  rw [dT0_eq_neg_lamPos, neg_ne_zero]

/-- The class of a relative 3-cycle of `(ℝ³, ℝ³ ∖ 0)` is its local degree times the library's
generator `(localTopIso 1).inv 1` of the local homology. -/
theorem relCls_eq_degRel_smul (c : AbF.obj ((chains E3).X 3)) (h : RelCycle (Punctured 3) c) :
    (relCls (Punctured 3) c h : (relativeChains (Punctured 3)).homology 3) =
      degRel c h • (localTopIso 1).inv.hom (1 : ℚ) := by
  have e : (localTopIso 1).inv.hom (degRel c h) = relCls (Punctured 3) c h := by
    change (localTopIso 1).inv.hom ((localTopIso 1).hom.hom (relCls (Punctured 3) c h)) = _
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id]
    rfl
  rw [← e]
  have : degRel c h = degRel c h • (1 : ℚ) := by simp
  conv_lhs => rw [this]
  rw [map_smul]

end Calibration

end TernaryPeriodPolynomials.Argument.Lemma33.Orient
