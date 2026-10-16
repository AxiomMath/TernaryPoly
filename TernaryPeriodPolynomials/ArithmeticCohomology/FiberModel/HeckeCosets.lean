module

public import Mathlib

@[expose] public section


/-!
# Hecke transfer for `diag(1,1,p)`: representatives, binary blocks, fibre indices

Paper: Appendix A.3 "The Hecke
transfer", and.  Everything here is stated for integral matrices.

* **H1** (`repT_mem`, `repT_inj`, `repT_complete`, and the binary analogue `repB_mem`, `repB_inj`,
  `repB_complete`): the `p² + p + 1` matrices `repT p i` (`(1 0 0; 0 1 0; b c p)`, `(1 0 0; a p 0; 0 0 1)`,
  `diag(p,1,1)`) are a complete irredundant set of representatives of the cosets `m · GL₃(ℤ)` in the double
  coset `GL₃(ℤ) diag(1,1,p) GL₃(ℤ)` (`DC3 p`); the `p + 1` binary blocks `C_c = (1 0; c p)`,
  `C_∞ = diag(p,1)` likewise for `GL₂(ℤ) diag(1,p) GL₂(ℤ)` (`DC2 p`).
* **H2** (`repT_block`, `repT_first_row`, `cOf_inl`, `fibre_card_c`, `fibre_card_inf`, `fibre_card_one`): each
  representative is `(λ 0; u C)` and preserves `H = {a = 0}`; the parameter `b` (resp. `a`) enters only
  the unipotent column `u`; exactly `p` representatives lie above each of `C_0, …, C_{p-1}, C_∞`, and one
  (`diag(p,1,1)`, normal scale `p`, block `I`) above `I`.
* **H3** (`latU`, `eIdx`, `eIdx_c`, `eIdx_inf`, `eIdx_one`, `quotient_reps_c`, `quotient_reps_inf`,
  `weights`): `U_t = ℤ² ∩ (C/λ)ℤ²`, `e_t = [ℤ² : U_t]` equals `p` for `λ = 1`, `C ∈ {C_c, C_∞}` and `1`
  for `λ = p`, `C = I`; the radical quotient `ℤ²/U_t` has the representatives `(0, b)` (for `C_c`),
  `(a, 0)` (for `C_∞`); `e_t λ² = p, p, p²`.
* **H4, formal part** (`transfer_sum_formal`): `∑_i λ_i² [C_i] = p(∑_c [C_c] + [C_∞]) + p² [I]`.
  The Hom-model statement `T₃(p,1)|_res = p T₂(p) + p² I` is `HeckeHom.lean`.
* **The lattice fixing `ℓ` contains `3 N_R`** (`threeNR_fixes_covector`, `threeLattice_zariskiDense`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open Matrix

variable (p : ℕ)

/-- The index set of the `p² + p + 1` representatives: `(b, c)` with `0 ≤ b, c < p`, then `a` with
`0 ≤ a < p`, then the diagonal one. -/
abbrev HeckeIdx : Type := (Fin p × Fin p) ⊕ (Fin p ⊕ Unit)

/-- The literal representatives of the right cosets of the double coset of `diag(1,1,p)`. -/
def repT : HeckeIdx p → Matrix (Fin 3) (Fin 3) ℤ
  | .inl (b, c) => !![1, 0, 0; 0, 1, 0; (b : ℤ), (c : ℤ), (p : ℤ)]
  | .inr (.inl a) => !![1, 0, 0; (a : ℤ), (p : ℤ), 0; 0, 0, 1]
  | .inr (.inr _) => !![(p : ℤ), 0, 0; 0, 1, 0; 0, 0, 1]

/-- `diag(1, 1, p)`. -/
def deltaT : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 1, 0; 0, 0, (p : ℤ)]

/-- The double coset `GL₃(ℤ) diag(1,1,p) GL₃(ℤ)` inside the integral matrices. -/
def DC3 : Set (Matrix (Fin 3) (Fin 3) ℤ) :=
  {g | ∃ a b : GL (Fin 3) ℤ, g = (a : Matrix (Fin 3) (Fin 3) ℤ) * deltaT p * (b : Matrix (Fin 3) (Fin 3) ℤ)}

/-- Lower unipotent with entries `x, y` in the bottom row. -/
def uBottom (x y : ℤ) : GL (Fin 3) ℤ :=
  ⟨!![1, 0, 0; 0, 1, 0; x, y, 1], !![1, 0, 0; 0, 1, 0; -x, -y, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- Lower unipotent with the entry `x` in position `(2,1)`. -/
def uMid (x : ℤ) : GL (Fin 3) ℤ :=
  ⟨!![1, 0, 0; x, 1, 0; 0, 0, 1], !![1, 0, 0; -x, 1, 0; 0, 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- The permutation matrix swapping the coordinates `2` and `3`. -/
def swap23 : GL (Fin 3) ℤ :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- The permutation matrix swapping the coordinates `1` and `3`. -/
def swap13 : GL (Fin 3) ℤ :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem repT_mem (i : HeckeIdx p) : repT p i ∈ DC3 p := by
  rcases i with ⟨b, c⟩ | a | u
  · refine ⟨uBottom b c, 1, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [repT, deltaT, uBottom, Matrix.mul_apply, Fin.sum_univ_three]
  · refine ⟨uMid a * swap23, swap23, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [repT, deltaT, uMid, swap23, Matrix.mul_apply, Fin.sum_univ_three]
  · refine ⟨swap13, swap13, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [repT, deltaT, swap13, Matrix.mul_apply, Fin.sum_univ_three]


theorem det_repT (i : HeckeIdx p) : (repT p i).det = p := by
  rcases i with ⟨b, c⟩ | a | u <;> simp [repT, Matrix.det_fin_three]

theorem adj_mul_repT_dvd (i j : HeckeIdx p) (γ : GL (Fin 3) ℤ)
    (h : repT p i = repT p j * (γ : Matrix (Fin 3) (Fin 3) ℤ)) (k l : Fin 3) :
    (p : ℤ) ∣ ((repT p j).adjugate * repT p i) k l := by
  have : (repT p j).adjugate * repT p i = (p : ℤ) • (γ : Matrix (Fin 3) (Fin 3) ℤ) := by
    rw [h, ← Matrix.mul_assoc, Matrix.adjugate_mul, det_repT]
    simp
  rw [this]
  exact ⟨γ k l, by simp⟩

theorem not_dvd_one_int [Fact p.Prime] : ¬ (p : ℤ) ∣ 1 := by
  intro h
  have h1 := Int.le_of_dvd one_pos h
  have h2 := (Fact.out : p.Prime).one_lt
  omega

theorem fin_eq_of_dvd {x y : Fin p} (h : (p : ℤ) ∣ (x : ℤ) - (y : ℤ)) : x = y := by
  have hx := x.2
  have hy := y.2
  have : (x : ℤ) = y := by
    obtain ⟨k, hk⟩ := h
    have hx' : (x : ℤ) < p := by exact_mod_cast hx
    have hy' : (y : ℤ) < p := by exact_mod_cast hy
    have hp : (0 : ℤ) < p := by
      have : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hx
      exact_mod_cast this
    have hk0 : k = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · nlinarith [Int.natCast_nonneg (x : ℕ), Int.natCast_nonneg (y : ℕ)]
      · nlinarith [Int.natCast_nonneg (x : ℕ), Int.natCast_nonneg (y : ℕ)]
    rw [hk0] at hk
    linarith
  exact Fin.ext (by exact_mod_cast this)

theorem repT_inj [Fact p.Prime] (i j : HeckeIdx p) (γ : GL (Fin 3) ℤ)
    (h : repT p i = repT p j * (γ : Matrix (Fin 3) (Fin 3) ℤ)) : i = j := by
  rcases i with ⟨b, c⟩ | a | u <;> rcases j with ⟨b', c'⟩ | a' | u'
  · have h1 := adj_mul_repT_dvd p _ _ γ h 2 0
    have h2 := adj_mul_repT_dvd p _ _ γ h 2 1
    simp [repT, Matrix.adjugate_fin_three_of, Matrix.mul_apply, Fin.sum_univ_three] at h1 h2
    have e1 : b = b' := fin_eq_of_dvd p (by simpa [sub_eq_add_neg, add_comm] using h1)
    have e2 : c = c' := fin_eq_of_dvd p (by simpa [sub_eq_add_neg, add_comm] using h2)
    rw [e1, e2]
  · have h1 := adj_mul_repT_dvd p _ _ γ h 1 1
    simp [repT, Matrix.adjugate_fin_three_of, Matrix.mul_apply, Fin.sum_univ_three] at h1
    exact absurd h1 (not_dvd_one_int p)
  · have h1 := adj_mul_repT_dvd p _ _ γ h 0 0
    simp [repT, Matrix.adjugate_fin_three_of, Matrix.mul_apply, Fin.sum_univ_three] at h1
    exact absurd h1 (not_dvd_one_int p)
  · have h1 := adj_mul_repT_dvd p _ _ γ h 2 2
    simp [repT, Matrix.adjugate_fin_three_of, Matrix.mul_apply, Fin.sum_univ_three] at h1
    exact absurd h1 (not_dvd_one_int p)
  · have h1 := adj_mul_repT_dvd p _ _ γ h 1 0
    simp [repT, Matrix.adjugate_fin_three_of, Matrix.mul_apply, Fin.sum_univ_three] at h1
    have e1 : a = a' := fin_eq_of_dvd p (by simpa [sub_eq_add_neg, add_comm] using h1)
    rw [e1]
  · have h1 := adj_mul_repT_dvd p _ _ γ h 0 0
    simp [repT, Matrix.adjugate_fin_three_of, Matrix.mul_apply, Fin.sum_univ_three] at h1
    exact absurd h1 (not_dvd_one_int p)
  · have h1 := adj_mul_repT_dvd p _ _ γ h 2 2
    simp [repT, Matrix.adjugate_fin_three_of, Matrix.mul_apply, Fin.sum_univ_three] at h1
    exact absurd h1 (not_dvd_one_int p)
  · have h1 := adj_mul_repT_dvd p _ _ γ h 1 1
    simp [repT, Matrix.adjugate_fin_three_of, Matrix.mul_apply, Fin.sum_univ_three] at h1
    exact absurd h1 (not_dvd_one_int p)
  · rfl

/-- Columns of `y` lie in the kernel of the covector `(-b, -c, 1)` modulo `p`. -/
theorem div_of_cov_bc (y : Matrix (Fin 3) (Fin 3) ℤ) (b c : Fin p)
    (h0 : (p : ℤ) ∣ y 2 0 - b * y 0 0 - c * y 1 0) (h1 : (p : ℤ) ∣ y 2 1 - b * y 0 1 - c * y 1 1) :
    ∀ k l, (p : ℤ) ∣ ((repT p (.inl (b, c))).adjugate * y * deltaT p) k l := by
  intro k l
  fin_cases k <;> fin_cases l <;>
    simp [repT, deltaT, Matrix.adjugate_fin_three_of, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  all_goals first
    | (convert h0 using 1; ring1)
    | (convert h1 using 1; ring1)

theorem div_of_cov_a (y : Matrix (Fin 3) (Fin 3) ℤ) (a : Fin p)
    (h0 : (p : ℤ) ∣ y 1 0 - a * y 0 0) (h1 : (p : ℤ) ∣ y 1 1 - a * y 0 1) :
    ∀ k l, (p : ℤ) ∣ ((repT p (.inr (.inl a))).adjugate * y * deltaT p) k l := by
  intro k l
  fin_cases k <;> fin_cases l <;>
    simp [repT, deltaT, Matrix.adjugate_fin_three_of, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  all_goals first
    | (convert h0 using 1; ring1)
    | (convert h1 using 1; ring1)

theorem div_of_cov_inf (y : Matrix (Fin 3) (Fin 3) ℤ)
    (h0 : (p : ℤ) ∣ y 0 0) (h1 : (p : ℤ) ∣ y 0 1) :
    ∀ k l, (p : ℤ) ∣ ((repT p (.inr (.inr ()))).adjugate * y * deltaT p) k l := by
  intro k l
  fin_cases k <;> fin_cases l <;>
    simp [repT, deltaT, Matrix.adjugate_fin_three_of, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  all_goals first
    | exact h0
    | exact h1

theorem coset_of_div [Fact p.Prime] (i : HeckeIdx p) (a b : GL (Fin 3) ℤ)
    (h : ∀ k l, (p : ℤ) ∣ ((repT p i).adjugate * (a : Matrix (Fin 3) (Fin 3) ℤ) * deltaT p) k l) :
    ∃ γ : GL (Fin 3) ℤ, (a : Matrix (Fin 3) (Fin 3) ℤ) * deltaT p * (b : Matrix (Fin 3) (Fin 3) ℤ) =
      repT p i * (γ : Matrix (Fin 3) (Fin 3) ℤ) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  choose Y hY using h
  let Y' : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of Y
  have hY' : (repT p i).adjugate * (a : Matrix (Fin 3) (Fin 3) ℤ) * deltaT p = (p : ℤ) • Y' := by
    ext k l; simp [Y', hY k l]
  have hm : repT p i * Y' = (a : Matrix (Fin 3) (Fin 3) ℤ) * deltaT p := by
    have h1 : (p : ℤ) • (repT p i * Y') = (p : ℤ) • ((a : Matrix (Fin 3) (Fin 3) ℤ) * deltaT p) := by
      calc (p : ℤ) • (repT p i * Y') = repT p i * ((p : ℤ) • Y') := by rw [Matrix.mul_smul]
        _ = repT p i * ((repT p i).adjugate * (a : Matrix (Fin 3) (Fin 3) ℤ) * deltaT p) := by rw [hY']
        _ = (repT p i * (repT p i).adjugate) * ((a : Matrix (Fin 3) (Fin 3) ℤ) * deltaT p) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_adjugate, det_repT]; simp
    exact smul_right_injective _ hp0 h1
  have hdet : IsUnit (Y' * (b : Matrix (Fin 3) (Fin 3) ℤ)).det := by
    have h2 : (p : ℤ) * (Y' * (b : Matrix (Fin 3) (Fin 3) ℤ)).det =
        (p : ℤ) * ((a : Matrix (Fin 3) (Fin 3) ℤ).det * (b : Matrix (Fin 3) (Fin 3) ℤ).det) := by
      have := congrArg Matrix.det (show repT p i * (Y' * (b : Matrix (Fin 3) (Fin 3) ℤ)) =
        (a : Matrix (Fin 3) (Fin 3) ℤ) * deltaT p * (b : Matrix (Fin 3) (Fin 3) ℤ) by
          rw [← Matrix.mul_assoc, hm])
      rw [Matrix.det_mul, det_repT] at this
      rw [this, Matrix.det_mul, Matrix.det_mul]
      have hd : (deltaT p).det = p := by simp [deltaT, Matrix.det_fin_three]
      rw [hd]; ring
    have h3 := mul_left_cancel₀ hp0 h2
    rw [h3]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 b.isUnit)
  refine ⟨Matrix.GeneralLinearGroup.mk'' _ hdet, ?_⟩
  simp only [Matrix.GeneralLinearGroup.val_mk'']
  rw [← Matrix.mul_assoc, hm]

/-- Linear algebra mod `p`: for an invertible integral matrix the plane spanned by its first two
columns is killed by one of the normalized covectors. -/
theorem exists_covector [Fact p.Prime] (y : GL (Fin 3) ℤ) :
    (∃ b c : Fin p, (p : ℤ) ∣ (y : Matrix (Fin 3) (Fin 3) ℤ) 2 0 - b * (y : Matrix (Fin 3) (Fin 3) ℤ) 0 0 -
        c * (y : Matrix (Fin 3) (Fin 3) ℤ) 1 0 ∧
      (p : ℤ) ∣ (y : Matrix (Fin 3) (Fin 3) ℤ) 2 1 - b * (y : Matrix (Fin 3) (Fin 3) ℤ) 0 1 -
        c * (y : Matrix (Fin 3) (Fin 3) ℤ) 1 1) ∨
    (∃ a : Fin p, (p : ℤ) ∣ (y : Matrix (Fin 3) (Fin 3) ℤ) 1 0 - a * (y : Matrix (Fin 3) (Fin 3) ℤ) 0 0 ∧
      (p : ℤ) ∣ (y : Matrix (Fin 3) (Fin 3) ℤ) 1 1 - a * (y : Matrix (Fin 3) (Fin 3) ℤ) 0 1) ∨
    ((p : ℤ) ∣ (y : Matrix (Fin 3) (Fin 3) ℤ) 0 0 ∧ (p : ℤ) ∣ (y : Matrix (Fin 3) (Fin 3) ℤ) 0 1) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set Y : Matrix (Fin 3) (Fin 3) ℤ := (y : Matrix (Fin 3) (Fin 3) ℤ) with hY
  set w1 : ZMod p := ((Y 1 0 * Y 2 1 - Y 2 0 * Y 1 1 : ℤ) : ZMod p) with hw1
  set w2 : ZMod p := ((Y 2 0 * Y 0 1 - Y 0 0 * Y 2 1 : ℤ) : ZMod p) with hw2
  set w3 : ZMod p := ((Y 0 0 * Y 1 1 - Y 1 0 * Y 0 1 : ℤ) : ZMod p) with hw3
  have hdet : (Y.det : ZMod p) = (Y 0 2 : ZMod p) * w1 + (Y 1 2 : ZMod p) * w2 + (Y 2 2 : ZMod p) * w3 := by
    simp only [hw1, hw2, hw3, Matrix.det_fin_three]
    push_cast; ring
  have hu : IsUnit (Y.det) := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have hne : (Y.det : ZMod p) ≠ 0 := by
    intro h0
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0
    exact not_dvd_one_int p (isUnit_iff_dvd_one.mp (isUnit_of_dvd_unit hdvd hu))
  have id0 : w1 * (Y 0 0 : ZMod p) + w2 * (Y 1 0 : ZMod p) + w3 * (Y 2 0 : ZMod p) = 0 := by
    simp only [hw1, hw2, hw3]; push_cast; ring
  have id1 : w1 * (Y 0 1 : ZMod p) + w2 * (Y 1 1 : ZMod p) + w3 * (Y 2 1 : ZMod p) = 0 := by
    simp only [hw1, hw2, hw3]; push_cast; ring
  by_cases h3 : w3 = 0
  · by_cases h2 : w2 = 0
    · have h1 : w1 ≠ 0 := by
        intro h1
        apply hne
        rw [hdet, h1, h2, h3]; ring
      right; right
      rw [h2, h3] at id0 id1
      have e0 : (Y 0 0 : ZMod p) = 0 := by
        have := id0; simp at this; exact this.resolve_left h1
      have e1 : (Y 0 1 : ZMod p) = 0 := by
        have := id1; simp at this; exact this.resolve_left h1
      exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 e0, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 e1⟩
    · right; left
      refine ⟨⟨(-w1 / w2).val, ZMod.val_lt _⟩, ?_, ?_⟩
      · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
        push_cast
        simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
        rw [h3] at id0
        field_simp
        linear_combination id0
      · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
        push_cast
        simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
        rw [h3] at id1
        field_simp
        linear_combination id1
  · left
    refine ⟨⟨(-w1 / w3).val, ZMod.val_lt _⟩, ⟨(-w2 / w3).val, ZMod.val_lt _⟩, ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
      field_simp
      linear_combination id0
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
      field_simp
      linear_combination id1

/-- **Completeness of the representatives.**  Every element of the double coset is a representative
times an element of `GL₃(ℤ)`. -/
theorem repT_complete [Fact p.Prime] (g : Matrix (Fin 3) (Fin 3) ℤ) (hg : g ∈ DC3 p) :
    ∃ (i : HeckeIdx p) (γ : GL (Fin 3) ℤ), g = repT p i * (γ : Matrix (Fin 3) (Fin 3) ℤ) := by
  obtain ⟨a, b, rfl⟩ := hg
  rcases exists_covector p a with ⟨bb, cc, h0, h1⟩ | ⟨aa, h0, h1⟩ | ⟨h0, h1⟩
  · obtain ⟨γ, hγ⟩ := coset_of_div p (.inl (bb, cc)) a b (div_of_cov_bc p _ bb cc h0 h1)
    exact ⟨_, γ, hγ⟩
  · obtain ⟨γ, hγ⟩ := coset_of_div p (.inr (.inl aa)) a b (div_of_cov_a p _ aa h0 h1)
    exact ⟨_, γ, hγ⟩
  · obtain ⟨γ, hγ⟩ := coset_of_div p (.inr (.inr ())) a b (div_of_cov_inf p _ h0 h1)
    exact ⟨_, γ, hγ⟩

/-! ### The binary analogue -/

/-- The index set of the `p + 1` binary representatives. -/
abbrev HeckeIdx2 : Type := Fin p ⊕ Unit

/-- The binary blocks `C_c = (1 0; c p)` and `C_∞ = (p 0; 0 1)`. -/
def repB : HeckeIdx2 p → Matrix (Fin 2) (Fin 2) ℤ
  | .inl c => !![1, 0; (c : ℤ), (p : ℤ)]
  | .inr _ => !![(p : ℤ), 0; 0, 1]

/-- `diag(1, p)`. -/
def deltaB : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (p : ℤ)]

/-- The double coset `GL₂(ℤ) diag(1,p) GL₂(ℤ)` inside the integral matrices. -/
def DC2 : Set (Matrix (Fin 2) (Fin 2) ℤ) :=
  {g | ∃ a b : GL (Fin 2) ℤ, g = (a : Matrix (Fin 2) (Fin 2) ℤ) * deltaB p * (b : Matrix (Fin 2) (Fin 2) ℤ)}

/-- Lower unipotent `(1 0; x 1)`. -/
def uLow2 (x : ℤ) : GL (Fin 2) ℤ :=
  ⟨!![1, 0; x, 1], !![1, 0; -x, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- The permutation matrix swapping the two coordinates. -/
def swap2 : GL (Fin 2) ℤ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem repB_mem (i : HeckeIdx2 p) : repB p i ∈ DC2 p := by
  rcases i with c | u
  · refine ⟨uLow2 c, 1, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [repB, deltaB, uLow2, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨swap2, swap2, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [repB, deltaB, swap2, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_repB (i : HeckeIdx2 p) : (repB p i).det = p := by
  rcases i with c | u <;> simp [repB, Matrix.det_fin_two]

theorem adj_mul_repB_dvd (i j : HeckeIdx2 p) (γ : GL (Fin 2) ℤ)
    (h : repB p i = repB p j * (γ : Matrix (Fin 2) (Fin 2) ℤ)) (k l : Fin 2) :
    (p : ℤ) ∣ ((repB p j).adjugate * repB p i) k l := by
  have : (repB p j).adjugate * repB p i = (p : ℤ) • (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [h, ← Matrix.mul_assoc, Matrix.adjugate_mul, det_repB]
    simp
  rw [this]
  exact ⟨γ k l, by simp⟩

theorem repB_inj [Fact p.Prime] (i j : HeckeIdx2 p) (γ : GL (Fin 2) ℤ)
    (h : repB p i = repB p j * (γ : Matrix (Fin 2) (Fin 2) ℤ)) : i = j := by
  rcases i with c | u <;> rcases j with c' | u'
  · have h1 := adj_mul_repB_dvd p _ _ γ h 1 0
    simp [repB, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h1
    have e1 : c = c' := fin_eq_of_dvd p (by simpa [sub_eq_add_neg, add_comm] using h1)
    rw [e1]
  · have h1 := adj_mul_repB_dvd p _ _ γ h 0 0
    simp [repB, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h1
    exact absurd h1 (not_dvd_one_int p)
  · have h1 := adj_mul_repB_dvd p _ _ γ h 1 1
    simp [repB, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h1
    exact absurd h1 (not_dvd_one_int p)
  · rfl

theorem div_of_cov_c (y : Matrix (Fin 2) (Fin 2) ℤ) (c : Fin p)
    (h0 : (p : ℤ) ∣ y 1 0 - c * y 0 0) :
    ∀ k l, (p : ℤ) ∣ ((repB p (.inl c)).adjugate * y * deltaB p) k l := by
  intro k l
  fin_cases k <;> fin_cases l <;>
    simp [repB, deltaB, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  all_goals first
    | (convert h0 using 1; ring1)

theorem div_of_cov_inf2 (y : Matrix (Fin 2) (Fin 2) ℤ) (h0 : (p : ℤ) ∣ y 0 0) :
    ∀ k l, (p : ℤ) ∣ ((repB p (.inr ())).adjugate * y * deltaB p) k l := by
  intro k l
  fin_cases k <;> fin_cases l <;>
    simp [repB, deltaB, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  all_goals first
    | exact h0

theorem coset_of_div2 [Fact p.Prime] (i : HeckeIdx2 p) (a b : GL (Fin 2) ℤ)
    (h : ∀ k l, (p : ℤ) ∣ ((repB p i).adjugate * (a : Matrix (Fin 2) (Fin 2) ℤ) * deltaB p) k l) :
    ∃ γ : GL (Fin 2) ℤ, (a : Matrix (Fin 2) (Fin 2) ℤ) * deltaB p * (b : Matrix (Fin 2) (Fin 2) ℤ) =
      repB p i * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  choose Y hY using h
  let Y' : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of Y
  have hY' : (repB p i).adjugate * (a : Matrix (Fin 2) (Fin 2) ℤ) * deltaB p = (p : ℤ) • Y' := by
    ext k l; simp [Y', hY k l]
  have hm : repB p i * Y' = (a : Matrix (Fin 2) (Fin 2) ℤ) * deltaB p := by
    have h1 : (p : ℤ) • (repB p i * Y') = (p : ℤ) • ((a : Matrix (Fin 2) (Fin 2) ℤ) * deltaB p) := by
      calc (p : ℤ) • (repB p i * Y') = repB p i * ((p : ℤ) • Y') := by rw [Matrix.mul_smul]
        _ = repB p i * ((repB p i).adjugate * (a : Matrix (Fin 2) (Fin 2) ℤ) * deltaB p) := by rw [hY']
        _ = (repB p i * (repB p i).adjugate) * ((a : Matrix (Fin 2) (Fin 2) ℤ) * deltaB p) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_adjugate, det_repB]; simp
    exact smul_right_injective _ hp0 h1
  have hdet : IsUnit (Y' * (b : Matrix (Fin 2) (Fin 2) ℤ)).det := by
    have h2 : (p : ℤ) * (Y' * (b : Matrix (Fin 2) (Fin 2) ℤ)).det =
        (p : ℤ) * ((a : Matrix (Fin 2) (Fin 2) ℤ).det * (b : Matrix (Fin 2) (Fin 2) ℤ).det) := by
      have := congrArg Matrix.det (show repB p i * (Y' * (b : Matrix (Fin 2) (Fin 2) ℤ)) =
        (a : Matrix (Fin 2) (Fin 2) ℤ) * deltaB p * (b : Matrix (Fin 2) (Fin 2) ℤ) by
          rw [← Matrix.mul_assoc, hm])
      rw [Matrix.det_mul, det_repB] at this
      rw [this, Matrix.det_mul, Matrix.det_mul]
      have hd : (deltaB p).det = p := by simp [deltaB, Matrix.det_fin_two]
      rw [hd]; ring
    have h3 := mul_left_cancel₀ hp0 h2
    rw [h3]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 b.isUnit)
  refine ⟨Matrix.GeneralLinearGroup.mk'' _ hdet, ?_⟩
  simp only [Matrix.GeneralLinearGroup.val_mk'']
  rw [← Matrix.mul_assoc, hm]

theorem exists_covector2 [Fact p.Prime] (y : GL (Fin 2) ℤ) :
    (∃ c : Fin p, (p : ℤ) ∣ (y : Matrix (Fin 2) (Fin 2) ℤ) 1 0 - c * (y : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ∨
    (p : ℤ) ∣ (y : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set Y : Matrix (Fin 2) (Fin 2) ℤ := (y : Matrix (Fin 2) (Fin 2) ℤ) with hY
  have hu : IsUnit (Y.det) := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  by_cases h0 : (Y 0 0 : ZMod p) = 0
  · right; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0
  · left
    refine ⟨⟨(Y 1 0 / Y 0 0 : ZMod p).val, ZMod.val_lt _⟩, ?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    field_simp
    ring

/-- **Completeness of the binary representatives.** -/
theorem repB_complete [Fact p.Prime] (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g ∈ DC2 p) :
    ∃ (i : HeckeIdx2 p) (γ : GL (Fin 2) ℤ), g = repB p i * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨a, b, rfl⟩ := hg
  rcases exists_covector2 p a with ⟨cc, h0⟩ | h0
  · obtain ⟨γ, hγ⟩ := coset_of_div2 p (.inl cc) a b (div_of_cov_c p _ cc h0)
    exact ⟨_, γ, hγ⟩
  · obtain ⟨γ, hγ⟩ := coset_of_div2 p (.inr ()) a b (div_of_cov_inf2 p _ h0)
    exact ⟨_, γ, hγ⟩

/-! ### H2: the block form and the fibres over the binary cosets -/

/-- The block matrix `(λ 0; u C)` with `λ` a scalar, `u` a column of height two and `C` a `2 × 2`
block. -/
def blockM (lam : ℤ) (u : Fin 2 → ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![lam, 0, 0; u 0, C 0 0, C 0 1; u 1, C 1 0, C 1 1]

/-- The normal scale `λ` of a representative. -/
def lamOf : HeckeIdx p → ℤ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => p

/-- The unipotent column `u` of a representative. -/
def uOf : HeckeIdx p → Fin 2 → ℤ
  | .inl (b, _) => ![0, (b : ℤ)]
  | .inr (.inl a) => ![(a : ℤ), 0]
  | .inr (.inr _) => 0

/-- The binary block `C` of a representative: `C_c`, `C_∞` or `I`. -/
def cOf : HeckeIdx p → Matrix (Fin 2) (Fin 2) ℤ
  | .inl (_, c) => repB p (.inl c)
  | .inr (.inl _) => repB p (.inr ())
  | .inr (.inr _) => 1

theorem repT_block (i : HeckeIdx p) : repT p i = blockM (lamOf p i) (uOf p i) (cOf p i) := by
  rcases i with ⟨b, c⟩ | a | u <;>
    · ext i j; fin_cases i <;> fin_cases j <;> simp [repT, blockM, lamOf, uOf, cOf, repB]

/-- Every representative preserves the hyperplane `a = 0`: its first row is `(λ, 0, 0)`. -/
theorem repT_first_row (i : HeckeIdx p) :
    repT p i 0 0 = lamOf p i ∧ repT p i 0 1 = 0 ∧ repT p i 0 2 = 0 := by
  rw [repT_block]; simp [blockM]

theorem det_blockM (lam : ℤ) (u : Fin 2 → ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) :
    (blockM lam u C).det = lam * C.det := by
  simp [blockM, Matrix.det_fin_three, Matrix.det_fin_two]; ring

/-- The binary block depends neither on `b` (first family) nor on `a` (second family). -/
theorem cOf_inl (b b' c : Fin p) : cOf p (.inl (b, c)) = cOf p (.inl (b', c)) := rfl

theorem repB_ne (c : Fin p) [Fact p.Prime] : repB p (.inl c) ≠ repB p (.inr ()) := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [repB] at this
  have h1 := (Fact.out : p.Prime).one_lt
  omega

theorem one_ne_repB_c (c : Fin p) [Fact p.Prime] : (1 : Matrix (Fin 2) (Fin 2) ℤ) ≠ repB p (.inl c) := by
  intro h
  have := congrFun (congrFun h 1) 1
  simp [repB] at this
  have h1 := (Fact.out : p.Prime).one_lt
  omega

theorem one_ne_repB_inf [Fact p.Prime] : (1 : Matrix (Fin 2) (Fin 2) ℤ) ≠ repB p (.inr ()) := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [repB] at this
  have h1 := (Fact.out : p.Prime).one_lt
  omega

theorem repB_inl_inj (c c' : Fin p) (h : repB p (.inl c) = repB p (.inl c')) : c = c' := by
  have := congrFun (congrFun h 1) 0
  simp [repB] at this
  exact Fin.ext (by exact_mod_cast this)

/-- Above each `C_c` lie exactly `p` representatives (one for each `b`). -/
theorem fibre_card_c [Fact p.Prime] (c : Fin p) :
    (Finset.univ.filter (fun i : HeckeIdx p => cOf p i = repB p (.inl c))).card = p := by
  have : Finset.univ.filter (fun i : HeckeIdx p => cOf p i = repB p (.inl c)) =
      Finset.univ.image (fun b : Fin p => (Sum.inl (b, c) : HeckeIdx p)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases i with ⟨b, c'⟩ | a | u
      · have : c' = c := repB_inl_inj p _ _ h
        exact ⟨b, by rw [this]⟩
      · exact absurd h.symm (repB_ne p c)
      · exact absurd h (one_ne_repB_c p c)
    · rintro ⟨b, rfl⟩
      rfl
  rw [this, Finset.card_image_of_injective _ (fun b b' h => by
    have := Sum.inl.inj h; exact congrArg Prod.fst this)]
  simp

/-- Above `C_∞` lie exactly `p` representatives (one for each `a`). -/
theorem fibre_card_inf [Fact p.Prime] :
    (Finset.univ.filter (fun i : HeckeIdx p => cOf p i = repB p (.inr ()))).card = p := by
  have : Finset.univ.filter (fun i : HeckeIdx p => cOf p i = repB p (.inr ())) =
      Finset.univ.image (fun a : Fin p => (Sum.inr (Sum.inl a) : HeckeIdx p)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases i with ⟨b, c'⟩ | a | u
      · exact absurd h (repB_ne p c')
      · exact ⟨a, rfl⟩
      · exact absurd h (one_ne_repB_inf p)
    · rintro ⟨a, rfl⟩
      rfl
  rw [this, Finset.card_image_of_injective _ (fun a a' h => by
    have := Sum.inr.inj h; exact Sum.inl.inj this)]
  simp

/-- Above the identity block lies exactly one representative, `diag(p,1,1)`. -/
theorem fibre_card_one [Fact p.Prime] :
    (Finset.univ.filter (fun i : HeckeIdx p => cOf p i = 1)).card = 1 := by
  have : Finset.univ.filter (fun i : HeckeIdx p => cOf p i = 1) = {Sum.inr (Sum.inr ())} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_singleton]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases i with ⟨b, c'⟩ | a | u
      · exact absurd h (one_ne_repB_c p c').symm
      · exact absurd h (one_ne_repB_inf p).symm
      · rfl
    · rintro rfl; rfl
  rw [this]; simp

/-! ### H3: the lattice `U_t` and the index `e_t` -/

/-- `U_t = ℤ² ∩ (C/λ) ℤ²` (for `λ ≠ 0`): the vectors `v ∈ ℤ²` with `λ v ∈ C ℤ²`. -/
def latU (lam : ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) : AddSubgroup (Fin 2 → ℤ) where
  carrier := {v | ∃ w : Fin 2 → ℤ, lam • v = C.mulVec w}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro v v' ⟨w, hw⟩ ⟨w', hw'⟩
    exact ⟨w + w', by rw [smul_add, hw, hw', Matrix.mulVec_add]⟩
  neg_mem' := by
    rintro v ⟨w, hw⟩
    exact ⟨-w, by rw [smul_neg, hw, Matrix.mulVec_neg]⟩

/-- The index `e_t = [ℤ² : U_t]`. -/
def eIdx (lam : ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := (latU lam C).index

theorem mem_latU {lam : ℤ} {C : Matrix (Fin 2) (Fin 2) ℤ} {v : Fin 2 → ℤ} :
    v ∈ latU lam C ↔ ∃ w : Fin 2 → ℤ, lam • v = C.mulVec w := Iff.rfl

/-- `U_t` for `λ = 1` and `C = C_c` is the kernel of `(x, y) ↦ y - c x` modulo `p`. -/
theorem mem_latU_c [Fact p.Prime] (c : Fin p) (v : Fin 2 → ℤ) :
    v ∈ latU 1 (repB p (.inl c)) ↔ (p : ℤ) ∣ v 1 - c * v 0 := by
  constructor
  · rintro ⟨w, hw⟩
    have h0 := congrFun hw 0
    have h1 := congrFun hw 1
    simp [repB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    exact ⟨w 1, by rw [← h0] at h1; linarith⟩
  · rintro ⟨k, hk⟩
    refine ⟨![v 0, k], ?_⟩
    ext i; fin_cases i
    · simp [repB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [repB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; linarith

theorem mem_latU_inf [Fact p.Prime] (v : Fin 2 → ℤ) :
    v ∈ latU 1 (repB p (.inr ())) ↔ (p : ℤ) ∣ v 0 := by
  constructor
  · rintro ⟨w, hw⟩
    have h0 := congrFun hw 0
    simp [repB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    exact ⟨w 0, h0⟩
  · rintro ⟨k, hk⟩
    refine ⟨![k, v 1], ?_⟩
    ext i; fin_cases i
    · simp [repB, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hk]
    · simp [repB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem latU_p_one [Fact p.Prime] : latU (p : ℤ) 1 = ⊤ := by
  ext v
  simp only [AddSubgroup.mem_top, iff_true]
  exact ⟨(p : ℤ) • v, by simp⟩

/-- `e_t = p` for `λ = 1`, `C = C_c`. -/
theorem eIdx_c [Fact p.Prime] (c : Fin p) : eIdx 1 (repB p (.inl c)) = p := by
  have hp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let φ : (Fin 2 → ℤ) →+ ZMod p :=
    { toFun := fun v => ((v 1 - c * v 0 : ℤ) : ZMod p)
      map_zero' := by simp
      map_add' := by intro v w; push_cast; simp; ring }
  have hker : φ.ker = latU 1 (repB p (.inl c)) := by
    ext v
    rw [AddMonoidHom.mem_ker, mem_latU_c]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _)
  have hsurj : Function.Surjective φ := by
    intro z
    refine ⟨![0, (z.val : ℤ)], ?_⟩
    simp [φ]
  unfold eIdx
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective _ hsurj]
  simp

/-- `e_t = p` for `λ = 1`, `C = C_∞`. -/
theorem eIdx_inf [Fact p.Prime] : eIdx 1 (repB p (.inr ())) = p := by
  have hp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let φ : (Fin 2 → ℤ) →+ ZMod p :=
    { toFun := fun v => ((v 0 : ℤ) : ZMod p)
      map_zero' := by simp
      map_add' := by intro v w; simp }
  have hker : φ.ker = latU 1 (repB p (.inr ())) := by
    ext v
    rw [AddMonoidHom.mem_ker, mem_latU_inf]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _)
  have hsurj : Function.Surjective φ := by
    intro z
    refine ⟨![(z.val : ℤ), 0], ?_⟩
    simp [φ]
  unfold eIdx
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective _ hsurj]
  simp

/-- `e_t = 1` for `λ = p`, `C = I`. -/
theorem eIdx_one [Fact p.Prime] : eIdx (p : ℤ) 1 = 1 := by
  unfold eIdx
  rw [latU_p_one]
  simp

/-- The classes of `ℤ²/U_t` for `C = C_c` are represented by `(0, b)`, `0 ≤ b < p`, uniquely. -/
theorem quotient_reps_c [Fact p.Prime] (c : Fin p) (v : Fin 2 → ℤ) :
    ∃! b : Fin p, v - ![0, (b : ℤ)] ∈ latU 1 (repB p (.inl c)) := by
  have hp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨⟨((v 1 - c * v 0 : ℤ) : ZMod p).val, ZMod.val_lt _⟩, ?_, ?_⟩
  · refine (mem_latU_c p c _).2 ?_
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    push_cast
    simp [ZMod.natCast_val] ; ring
  · intro b' hb'
    rw [mem_latU_c] at hb'
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hb'
    push_cast at h
    simp at h
    apply Fin.ext
    have : ((b' : ℕ) : ZMod p) = ((v 1 - c * v 0 : ℤ) : ZMod p) := by
      push_cast; linear_combination -h
    rw [← ZMod.val_natCast_of_lt b'.2, this]

/-- The classes of `ℤ²/U_t` for `C = C_∞` are represented by `(a, 0)`, `0 ≤ a < p`, uniquely. -/
theorem quotient_reps_inf [Fact p.Prime] (v : Fin 2 → ℤ) :
    ∃! a : Fin p, v - ![(a : ℤ), 0] ∈ latU 1 (repB p (.inr ())) := by
  have hp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨⟨((v 0 : ℤ) : ZMod p).val, ZMod.val_lt _⟩, ?_, ?_⟩
  · refine (mem_latU_inf p _).2 ?_
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    push_cast
    simp [ZMod.natCast_val]
  · intro a' ha'
    rw [mem_latU_inf] at ha'
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ha'
    push_cast at h
    simp at h
    apply Fin.ext
    have : ((a' : ℕ) : ZMod p) = ((v 0 : ℤ) : ZMod p) := by
      linear_combination -h
    rw [← ZMod.val_natCast_of_lt a'.2, this]

/-- **The weights.**  `e_t λ² = p` for the first two families and `e_t λ² = p²` for `diag(p,1,1)`; in
particular `e_t` is the number of representatives above the binary coset and the representatives
already constitute the transfer sum. -/
theorem weights [Fact p.Prime] :
    (∀ c : Fin p, eIdx 1 (repB p (.inl c)) * 1 ^ 2 = p) ∧
      eIdx 1 (repB p (.inr ())) * 1 ^ 2 = p ∧ eIdx (p : ℤ) 1 * (p : ℕ) ^ 2 = p ^ 2 := by
  refine ⟨fun c => by rw [eIdx_c]; simp, by rw [eIdx_inf]; simp, by rw [eIdx_one]; ring⟩

/-! ### H4 (formal): the transfer sum -/

/-- **The transfer sum as a formal combination of binary blocks.**  Summing `λ²` times the binary block
over the `p² + p + 1` representatives gives `p (∑_c [C_c] + [C_∞]) + p² [I]`, where `[C]` is the
formal symbol of the block `C`.  In the Hecke correspondence `[C]` becomes the usual binary
double-coset correspondence, and this is the formal skeleton of `T₃(p,1)|_res = p T₂(p) + p² I`. -/
theorem transfer_sum_formal :
    ∑ i : HeckeIdx p, (lamOf p i) ^ 2 • Finsupp.single (cOf p i) (1 : ℤ) =
      (p : ℤ) • (∑ c : Fin p, Finsupp.single (repB p (.inl c)) (1 : ℤ) +
        Finsupp.single (repB p (.inr ())) (1 : ℤ)) +
      (p : ℤ) ^ 2 • Finsupp.single (1 : Matrix (Fin 2) (Fin 2) ℤ) (1 : ℤ) := by
  simp only [HeckeIdx, Fintype.sum_sum_type, Fintype.sum_prod_type, lamOf, cOf, one_pow,
    one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.univ_unique]
  simp [smul_add, Finset.smul_sum, add_assoc]

/-! ### The lattice fixing a covector contains `3 N_R` -/

/-- The unipotent radical `N_P ≅ ℤ²` of the stabilizer of a line: `I + x E₁₂ + y E₁₃`. -/
def radP (x y : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, x, y; 0, 1, 0; 0, 0, 1]

/-- The unipotent radical `N_Q ≅ ℤ²` of the stabilizer of a plane: `I + x E₁₃ + y E₂₃`. -/
def radQ (x y : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, x; 0, 1, y; 0, 0, 1]

theorem radP_mul (x y x' y' : ℤ) : radP x y * radP x' y' = radP (x + x') (y + y') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [radP, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem radQ_mul (x y x' y' : ℤ) : radQ x y * radQ x' y' = radQ (x + x') (y + y') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [radQ, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- **The lattice fixing `ℓ` contains `3 N_R`.**  Every element `I + 3X` of `3 N_R` (here `N_R = N_P`
or `N_Q`, identified with `ℤ²`) fixes every covector `ℓ` modulo three, that is, lies in the lattice
fixing `ℓ`. -/
theorem threeNR_fixes_covector (x y : ℤ) (ℓ : Fin 3 → ZMod 3) :
    ℓ ᵥ* (radP (3 * x) (3 * y)).map (Int.castRingHom (ZMod 3)) = ℓ ∧
      ℓ ᵥ* (radQ (3 * x) (3 * y)).map (Int.castRingHom (ZMod 3)) = ℓ := by
  have h3' : (3 : ZMod 3) = 0 := by decide
  constructor <;> ext j <;> fin_cases j <;>
    simp [radP, radQ, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h3']

/-- **Zariski density of `3ℤ²`.**  A polynomial in two variables vanishing on the lattice `3ℤ²` is
zero; hence a lattice containing `3 N_R` is Zariski dense in the algebraic radical `N_R ≅ 𝔾ₐ²`. -/
theorem threeLattice_zariskiDense (P : MvPolynomial (Fin 2) ℚ)
    (h : ∀ a b : ℤ, MvPolynomial.eval ![(3 * a : ℚ), 3 * b] P = 0) : P = 0 := by
  have hinf : (Set.range (fun a : ℤ => (3 * a : ℚ))).Infinite :=
    Set.infinite_range_of_injective (fun a b hab => by
      have : (a : ℚ) = b := by linarith
      exact_mod_cast this)
  refine MvPolynomial.funext_set (q := 0) (fun _ => Set.range (fun a : ℤ => (3 * a : ℚ)))
    (fun _ => hinf) ?_
  intro x hx
  have h0 := hx 0 (Set.mem_univ _)
  have h1 := hx 1 (Set.mem_univ _)
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  have : x = ![(3 * a : ℚ), 3 * b] := by
    ext i; fin_cases i
    · exact ha.symm
    · exact hb.symm
  rw [this, h a b]
  simp

end TernaryPeriodPolynomials.Argument.FiberModel
