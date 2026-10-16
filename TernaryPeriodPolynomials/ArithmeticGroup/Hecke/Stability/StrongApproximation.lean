module

public import Mathlib

@[expose] public section


/-!
# Surjectivity of `SL_k(ℤ) → SL_k(ℤ/N)`

This is the finite-level form of strong approximation for `SL_k` used for
comparing rational and adelic double-coset decompositions. The proof is the
classical elementary-matrix argument: `ZMod N` has stable range one, so every
unimodular column can be moved to `e₀` by unipotent triangular matrices with
integral lifts, and induction on the size finishes.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open Matrix

namespace TernaryPeriodPolynomials.HeckeStability.StrongApproximation

section Units

variable {N : ℕ}

theorem isUnit_of_forall_prime [NeZero N] (z : ZMod N)
    (h : ∀ p : ℕ, p.Prime → ∀ hp : p ∣ N, ZMod.castHom hp (ZMod p) z ≠ 0) : IsUnit z := by
  rw [← ZMod.natCast_zmod_val z, ZMod.isUnit_iff_coprime]
  apply Nat.coprime_of_dvd
  intro p hp hpz hpN
  apply h p hp hpN
  rw [← ZMod.natCast_zmod_val z, map_natCast, ZMod.natCast_eq_zero_iff]
  exact hpz

/-- `ZMod N` (for `N ≠ 0`) has stable range one. -/
theorem exists_isUnit_add_mul [NeZero N] (a b x y : ZMod N) (h : x * a + y * b = 1) :
    ∃ s : ZMod N, IsUnit (a + s * b) := by
  classical
  refine ⟨∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ a.val), (p : ZMod N), ?_⟩
  apply isUnit_of_forall_prime
  intro p hp hpN
  have : Fact p.Prime := ⟨hp⟩
  have hφa : ZMod.castHom hpN (ZMod p) a = ((a.val : ℕ) : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    exact map_natCast _ _
  rw [map_add, map_mul, map_prod]
  simp only [map_natCast]
  by_cases hpa : p ∣ a.val
  · have ha0 : ZMod.castHom hpN (ZMod p) a = 0 := by
      rw [hφa, ZMod.natCast_eq_zero_iff]; exact hpa
    rw [ha0, zero_add]
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      intro q hq
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hq
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hpq
      have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq.1.1).mp hpq
      subst hpq'
      exact hq.2 hpa
    · intro hb
      have := congrArg (ZMod.castHom hpN (ZMod p)) h
      rw [map_add, map_mul, map_mul, ha0, hb, map_one] at this
      simp at this
  · rw [Finset.prod_eq_zero (i := p)]
    · rw [zero_mul, add_zero, hφa, Ne, ZMod.natCast_eq_zero_iff]; exact hpa
    · rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hp, hpN, NeZero.ne N⟩, hpa⟩
    · exact ZMod.natCast_self p

end Units

section Ops

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The block matrix `[[1, t], [0, 1]]`. -/
def upperOp (t : Fin (m + 1) → R) : Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  Matrix.of fun i j =>
    Fin.cases (motive := fun _ => R) (Fin.cases (motive := fun _ => R) 1 t j)
      (fun i' => Fin.cases (motive := fun _ => R) 0
        (fun j' => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) i' j') j) i

/-- The block matrix `[[1, 0], [t, 1]]`. -/
def lowerOp (t : Fin (m + 1) → R) : Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  Matrix.of fun i j =>
    Fin.cases (motive := fun _ => R) (Fin.cases (motive := fun _ => R) 1 0 j)
      (fun i' => Fin.cases (motive := fun _ => R) (t i')
        (fun j' => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) i' j') j) i

/-- The block matrix `[[1, 0], [0, B]]`. -/
def blockOne (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R) : Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  Matrix.of fun i j =>
    Fin.cases (motive := fun _ => R) (Fin.cases (motive := fun _ => R) 1 0 j)
      (fun i' => Fin.cases (motive := fun _ => R) 0 (fun j' => B i' j') j) i

@[simp] theorem upperOp_zero_zero (t : Fin (m + 1) → R) : upperOp t 0 0 = 1 := rfl
@[simp] theorem upperOp_zero_succ (t : Fin (m + 1) → R) (j : Fin (m + 1)) :
    upperOp t 0 j.succ = t j := rfl
@[simp] theorem upperOp_succ_zero (t : Fin (m + 1) → R) (i : Fin (m + 1)) :
    upperOp t i.succ 0 = 0 := rfl
@[simp] theorem upperOp_succ_succ (t : Fin (m + 1) → R) (i j : Fin (m + 1)) :
    upperOp t i.succ j.succ = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) i j := rfl

@[simp] theorem lowerOp_zero_zero (t : Fin (m + 1) → R) : lowerOp t 0 0 = 1 := rfl
@[simp] theorem lowerOp_zero_succ (t : Fin (m + 1) → R) (j : Fin (m + 1)) :
    lowerOp t 0 j.succ = 0 := rfl
@[simp] theorem lowerOp_succ_zero (t : Fin (m + 1) → R) (i : Fin (m + 1)) :
    lowerOp t i.succ 0 = t i := rfl
@[simp] theorem lowerOp_succ_succ (t : Fin (m + 1) → R) (i j : Fin (m + 1)) :
    lowerOp t i.succ j.succ = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) i j := rfl

@[simp] theorem blockOne_zero_zero (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    blockOne B 0 0 = 1 := rfl
@[simp] theorem blockOne_zero_succ (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (j : Fin (m + 1)) :
    blockOne B 0 j.succ = 0 := rfl
@[simp] theorem blockOne_succ_zero (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (i : Fin (m + 1)) :
    blockOne B i.succ 0 = 0 := rfl
@[simp] theorem blockOne_succ_succ (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (i j : Fin (m + 1)) :
    blockOne B i.succ j.succ = B i j := rfl

theorem det_of_col_zero (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R)
    (h : ∀ i : Fin (m + 1), A i.succ 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

theorem det_of_row_zero (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R)
    (h : ∀ j : Fin (m + 1), A 0 j.succ = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  simp [h]

theorem det_upperOp (t : Fin (m + 1) → R) : (upperOp t).det = 1 := by
  rw [det_of_col_zero _ (upperOp_succ_zero t)]
  have : (upperOp t).submatrix Fin.succ Fin.succ = 1 := by
    ext i j; simp
  rw [this, det_one, upperOp_zero_zero, one_mul]

theorem det_lowerOp (t : Fin (m + 1) → R) : (lowerOp t).det = 1 := by
  rw [det_of_row_zero _ (lowerOp_zero_succ t)]
  have : (lowerOp t).submatrix Fin.succ Fin.succ = 1 := by
    ext i j; simp
  rw [this, det_one, lowerOp_zero_zero, one_mul]

theorem det_blockOne (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R) : (blockOne B).det = B.det := by
  rw [det_of_col_zero _ (blockOne_succ_zero B)]
  have : (blockOne B).submatrix Fin.succ Fin.succ = B := by
    ext i j; simp
  rw [this, blockOne_zero_zero, one_mul]

theorem upperOp_map {S : Type*} [CommRing S] (f : R →+* S) (t : Fin (m + 1) → R) :
    (upperOp t).map f = upperOp (fun j => f (t j)) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, apply_ite f]

theorem lowerOp_map {S : Type*} [CommRing S] (f : R →+* S) (t : Fin (m + 1) → R) :
    (lowerOp t).map f = lowerOp (fun j => f (t j)) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, apply_ite f]

theorem blockOne_map {S : Type*} [CommRing S] (f : R →+* S)
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    (blockOne B).map f = blockOne (B.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem upperOp_mulVec_zero (t : Fin (m + 1) → R) (v : Fin (m + 2) → R) :
    (upperOp t *ᵥ v) 0 = v 0 + ∑ j, t j * v j.succ := by
  rw [mulVec, dotProduct, Fin.sum_univ_succ]
  simp

theorem upperOp_mulVec_succ (t : Fin (m + 1) → R) (v : Fin (m + 2) → R) (i : Fin (m + 1)) :
    (upperOp t *ᵥ v) i.succ = v i.succ := by
  rw [mulVec, dotProduct, Fin.sum_univ_succ]
  simp [Matrix.one_apply]

theorem lowerOp_mulVec_zero (t : Fin (m + 1) → R) (v : Fin (m + 2) → R) :
    (lowerOp t *ᵥ v) 0 = v 0 := by
  rw [mulVec, dotProduct, Fin.sum_univ_succ]
  simp

theorem lowerOp_mulVec_succ (t : Fin (m + 1) → R) (v : Fin (m + 2) → R) (i : Fin (m + 1)) :
    (lowerOp t *ᵥ v) i.succ = t i * v 0 + v i.succ := by
  rw [mulVec, dotProduct, Fin.sum_univ_succ]
  simp [Matrix.one_apply]

/-- `upperOp` as an element of `SL`. -/
def upperSL (t : Fin (m + 1) → R) : Matrix.SpecialLinearGroup (Fin (m + 2)) R :=
  ⟨upperOp t, det_upperOp t⟩

/-- `lowerOp` as an element of `SL`. -/
def lowerSL (t : Fin (m + 1) → R) : Matrix.SpecialLinearGroup (Fin (m + 2)) R :=
  ⟨lowerOp t, det_lowerOp t⟩

end Ops

section Reduction

variable {N : ℕ}

/-- The image of `SL_k(ℤ)` in `SL_k(ℤ/N)`. -/
abbrev intImage (N k : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin k) (ZMod N)) :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))).range

theorem cast_val_int [NeZero N] (c : ZMod N) : (((c.val : ℕ) : ℤ) : ZMod N) = c := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem upperSL_mem [NeZero N] {m : ℕ} (t : Fin (m + 1) → ZMod N) :
    upperSL t ∈ intImage N (m + 2) := by
  refine ⟨upperSL (fun j => (((t j).val : ℕ) : ℤ)), Subtype.ext ?_⟩
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  change (upperOp _).map _ = upperOp t
  rw [upperOp_map]
  congr 1
  funext j
  exact cast_val_int (t j)

theorem lowerSL_mem [NeZero N] {m : ℕ} (t : Fin (m + 1) → ZMod N) :
    lowerSL t ∈ intImage N (m + 2) := by
  refine ⟨lowerSL (fun j => (((t j).val : ℕ) : ℤ)), Subtype.ext ?_⟩
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  change (lowerOp _).map _ = lowerOp t
  rw [lowerOp_map]
  congr 1
  funext j
  exact cast_val_int (t j)

/-- Every unimodular column can be moved to `e₀` by an element of the image of `SL(ℤ)`. -/
theorem exists_mulVec_eq_single [NeZero N] {m : ℕ} (v w : Fin (m + 2) → ZMod N)
    (hw : ∑ i, w i * v i = 1) :
    ∃ E ∈ intImage N (m + 2), (E : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) *ᵥ v =
      Pi.single 0 1 := by
  classical
  rw [Fin.sum_univ_succ] at hw
  obtain ⟨s, hs⟩ := exists_isUnit_add_mul (v 0) (∑ j : Fin (m + 1), w j.succ * v j.succ) (w 0) 1
    (by rw [one_mul]; exact hw)
  obtain ⟨u, hu⟩ := hs
  let E1 := upperSL (fun j : Fin (m + 1) => s * w j.succ)
  let v1 := (E1 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) *ᵥ v
  have hv10 : v1 0 = u := by
    change (upperOp _ *ᵥ v) 0 = u
    rw [upperOp_mulVec_zero, hu, Finset.mul_sum]
    simp only [mul_assoc]
  let E2 := lowerSL (fun i : Fin (m + 1) => -(v1 i.succ) * ↑u⁻¹)
  let v2 := (E2 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) *ᵥ v1
  have hv20 : v2 0 = u := by
    change (lowerOp _ *ᵥ v1) 0 = u
    rw [lowerOp_mulVec_zero, hv10]
  have hv2s : ∀ i : Fin (m + 1), v2 i.succ = 0 := by
    intro i
    change (lowerOp _ *ᵥ v1) i.succ = 0
    rw [lowerOp_mulVec_succ, hv10, Units.inv_mul_cancel_right, neg_add_cancel]
  let E3 := lowerSL (Pi.single (0 : Fin (m + 1)) (1 : ZMod N))
  let v3 := (E3 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) *ᵥ v2
  have hv30 : v3 0 = u := by
    change (lowerOp _ *ᵥ v2) 0 = u
    rw [lowerOp_mulVec_zero, hv20]
  have hv3s : ∀ i : Fin (m + 1), v3 i.succ = (Pi.single (0 : Fin (m + 1)) (u : ZMod N) : Fin (m + 1) → ZMod N) i := by
    intro i
    change (lowerOp _ *ᵥ v2) i.succ = _
    rw [lowerOp_mulVec_succ, hv20, hv2s, add_zero]
    by_cases hi : i = 0
    · subst hi; simp
    · simp [hi]
  let E4 := upperSL (Pi.single (0 : Fin (m + 1)) ((↑u⁻¹ : ZMod N) - 1))
  let v4 := (E4 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) *ᵥ v3
  have hv40 : v4 0 = 1 := by
    change (upperOp _ *ᵥ v3) 0 = 1
    rw [upperOp_mulVec_zero, hv30]
    simp only [hv3s, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    rw [sub_mul, Units.inv_mul, one_mul]
    ring
  have hv4s : ∀ i : Fin (m + 1), v4 i.succ = (Pi.single (0 : Fin (m + 1)) (u : ZMod N) : Fin (m + 1) → ZMod N) i := by
    intro i
    change (upperOp _ *ᵥ v3) i.succ = _
    rw [upperOp_mulVec_succ, hv3s]
  let E5 := lowerSL (Pi.single (0 : Fin (m + 1)) (-(u : ZMod N)))
  let v5 := (E5 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) *ᵥ v4
  have hv5 : v5 = Pi.single 0 1 := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · change (lowerOp _ *ᵥ v4) 0 = _
      rw [lowerOp_mulVec_zero, hv40]; simp
    · change (lowerOp _ *ᵥ v4) i.succ = _
      rw [lowerOp_mulVec_succ, hv40, hv4s]
      rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i)]
      by_cases hi : i = 0
      · subst hi; simp
      · simp [hi]
  refine ⟨E5 * E4 * E3 * E2 * E1, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem (mul_mem (lowerSL_mem _) (upperSL_mem _)) (lowerSL_mem _))
      (lowerSL_mem _)) (upperSL_mem _)
  · rw [← hv5]
    simp only [Matrix.SpecialLinearGroup.coe_mul, v5, v4, v3, v2, v1, mulVec_mulVec, Matrix.mul_assoc]

theorem mem_intImage_one [NeZero N] (A : Matrix.SpecialLinearGroup (Fin 1) (ZMod N)) :
    A ∈ intImage N 1 := by
  have hA : A = 1 := by
    ext i j
    have h := A.2
    rw [det_unique] at h
    rw [Subsingleton.elim i default, Subsingleton.elim j default, h]
    rfl
  rw [hA]
  exact one_mem _

theorem mem_intImage [NeZero N] : ∀ (m : ℕ) (A : Matrix.SpecialLinearGroup (Fin (m + 1)) (ZMod N)),
    A ∈ intImage N (m + 1)
  | 0, A => mem_intImage_one A
  | m + 1, A => by
    classical
    -- First column reduction.
    have hw : ∑ i, (A⁻¹ : Matrix.SpecialLinearGroup _ _) 0 i * A i 0 = 1 := by
      have h : ((A⁻¹ * A : Matrix.SpecialLinearGroup (Fin (m + 2)) (ZMod N)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) 0 0 = 1 := by
        rw [inv_mul_cancel]; rfl
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply] at h
      exact h
    obtain ⟨E, hE, hEv⟩ := exists_mulVec_eq_single (fun i => A i 0) (fun i => (A⁻¹ : Matrix.SpecialLinearGroup _ _) 0 i) hw
    set A1 := E * A with hA1
    have hcol : ∀ i, (A1 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) i 0 = (Pi.single 0 1 : Fin (m + 2) → ZMod N) i := by
      intro i
      rw [← hEv, hA1, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      rfl
    -- Row clearing.
    let U := upperSL (fun j : Fin (m + 1) => -(A1 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) 0 j.succ)
    set C := A1 * U with hC
    have hC_mul : ∀ i j, (C : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) i j =
        (A1 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) i 0 * upperOp (fun j : Fin (m + 1) =>
          -(A1 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) 0 j.succ) 0 j +
        ∑ k : Fin (m + 1), (A1 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) i k.succ *
          upperOp (fun j : Fin (m + 1) => -(A1 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) 0 j.succ) k.succ j := by
      intro i j
      rw [hC, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ]
      rfl
    have hC00 : (C : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) 0 0 = 1 := by
      rw [hC_mul]; simp [hcol]
    have hCs0 : ∀ i : Fin (m + 1), (C : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) i.succ 0 = 0 := by
      intro i; rw [hC_mul]; simp [hcol]
    have hC0s : ∀ j : Fin (m + 1), (C : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)) 0 j.succ = 0 := by
      intro j; rw [hC_mul]; simp [hcol, Matrix.one_apply]
    let C' : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod N) :=
      (C : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N)).submatrix Fin.succ Fin.succ
    have hC'det : C'.det = 1 := by
      have h := C.2
      rw [det_of_col_zero _ hCs0, hC00, one_mul] at h
      exact h
    obtain ⟨B', hB'⟩ := mem_intImage m ⟨C', hC'det⟩
    have hCmem : C ∈ intImage N (m + 2) := by
      refine ⟨⟨blockOne (B' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ), by
        rw [det_blockOne]; exact Matrix.SpecialLinearGroup.det_coe B'⟩, Subtype.ext ?_⟩
      change (blockOne (B' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)).map (Int.castRingHom (ZMod N)) =
        (C : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod N))
      rw [blockOne_map]
      have hB'v : (B' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ).map (Int.castRingHom (ZMod N)) = C' := by
        have := congrArg Subtype.val hB'
        rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at this
        exact this
      rw [hB'v]
      ext i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [hC00]
      · simp [hC0s]
      · simp [hCs0]
      · simp [C']
    have hA : A = E⁻¹ * C * U⁻¹ := by
      rw [hC, hA1]; group
    rw [hA]
    exact mul_mem (mul_mem (inv_mem hE) hCmem) (inv_mem (upperSL_mem _))

/-- Strong approximation at finite level: `SL_k(ℤ) → SL_k(ℤ/N)` is surjective. -/
theorem map_intCast_surjective (N k : ℕ) [NeZero N] :
    Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) :
      Matrix.SpecialLinearGroup (Fin k) ℤ →* Matrix.SpecialLinearGroup (Fin k) (ZMod N)) := by
  intro A
  cases k with
  | zero =>
    refine ⟨1, Subtype.ext ?_⟩
    exact Subsingleton.elim _ _
  | succ m =>
    obtain ⟨B, hB⟩ := mem_intImage m A
    exact ⟨B, hB⟩

end Reduction

end TernaryPeriodPolynomials.HeckeStability.StrongApproximation
