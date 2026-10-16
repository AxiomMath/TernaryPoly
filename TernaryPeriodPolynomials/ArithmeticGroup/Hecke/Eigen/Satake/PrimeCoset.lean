module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.Coset
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.IntegerSmith

@[expose] public section


/-!
# The `GL₃(ℤ)` double coset of `diag(p, 1, 1)`

For a prime `p`, a rational `3 × 3` matrix lies in `GL₃(ℤ) diag(p,1,1) GL₃(ℤ)` if and only if it
is integral with determinant `±p` (integer Smith normal form).

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {p : ℕ}

/-- `diag(p, 1, 1)` in `GL₃(ℚ)`. -/
def gP (hp : p.Prime) : RationalGL3 :=
  ⟨diagonal ![(p : ℚ), 1, 1], diagonal ![(p : ℚ)⁻¹, 1, 1], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    fin_cases i <;> simp [this], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    fin_cases i <;> simp [this]⟩

/-- An integral unimodular matrix as an element of `Γ`. -/
def intUnit (M M' : Matrix (Fin 3) (Fin 3) ℤ) (h : M * M' = 1) : IntegralGL :=
  ⟨M, M', h, mul_eq_one_comm.mp h⟩

theorem intUnit_val (M M' : Matrix (Fin 3) (Fin 3) ℤ) (h : M * M' = 1) :
    (integralRational (intUnit M M' h)).val = M.map (Int.cast : ℤ → ℚ) := rfl

theorem sq_one_of_natAbs {z : ℤ} (h : z.natAbs = 1) : z * z = 1 := by
  rcases Int.natAbs_eq z with hz | hz <;> rw [hz, h] <;> norm_num

/-- A diagonal integer matrix with determinant `±p` is `P · diag(p,1,1) · P'` with `P, P'`
unimodular. -/
theorem prime_diagonal (hp : p.Prime) (a : Fin 3 → ℤ) (h : (a 0 * a 1 * a 2).natAbs = p) :
    ∃ P P₁ P' P₁' : Matrix (Fin 3) (Fin 3) ℤ, P * P₁ = 1 ∧ P' * P₁' = 1 ∧
      diagonal a = P * diagonal ![(p : ℤ), 1, 1] * P' := by
  rw [Int.natAbs_mul, Int.natAbs_mul] at h
  -- a sign-normalized diagonal unit
  have key : ∀ b : Fin 3 → ℤ, b 0 = (b 0 / p) * p → (b 0 / p) * (b 0 / p) = 1 →
      b 1 * b 1 = 1 → b 2 * b 2 = 1 →
      ∃ U : Matrix (Fin 3) (Fin 3) ℤ, U * U = 1 ∧ diagonal b = U * diagonal ![(p : ℤ), 1, 1] := by
    intro b h0 e0 e1 e2
    refine ⟨diagonal ![b 0 / p, b 1, b 2], ?_, ?_⟩
    · rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext i; fin_cases i <;> simp [e0, e1, e2]
    · rw [diagonal_mul_diagonal]
      congr 1; funext i; fin_cases i <;> simp [← h0]
  have hdiv : ∀ z : ℤ, z.natAbs = p → z = (z / p) * p ∧ (z / p) * (z / p) = 1 := by
    intro z hz
    have hd : (p : ℤ) ∣ z := by
      rw [← Int.natAbs_dvd_natAbs]; simp [hz]
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    refine ⟨(Int.ediv_mul_cancel hd).symm, ?_⟩
    have habs : (z / p).natAbs = 1 := by
      have := Int.natAbs_mul (z / p) p
      rw [Int.ediv_mul_cancel hd, hz, Int.natAbs_natCast] at this
      have hp1 : 0 < p := hp.pos
      nlinarith [this]
    exact sq_one_of_natAbs habs
  rcases Nat.prime_mul_iff.mp (h ▸ hp) with ⟨h01, h2⟩ | ⟨h2, h01⟩
  · rcases Nat.prime_mul_iff.mp h01 with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · -- `a 0 = ±p`
      have h0' : (a 0).natAbs = p := by
        have := h; rw [h1, h2, mul_one, mul_one] at this; exact this
      obtain ⟨d0, e0⟩ := hdiv _ h0'
      obtain ⟨U, hU, hUd⟩ := key a d0 e0 (sq_one_of_natAbs h1) (sq_one_of_natAbs h2)
      exact ⟨U, U, 1, 1, hU, mul_one 1, by rw [hUd, Matrix.mul_one]⟩
    · -- `a 1 = ±p`
      have h1' : (a 1).natAbs = p := by
        have := h; rw [h0, h2, one_mul, mul_one] at this; exact this
      obtain ⟨d1, e1⟩ := hdiv _ h1'
      let σ : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
      have hσ : σ * σ = 1 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [σ, Matrix.mul_apply, Fin.sum_univ_three]
      obtain ⟨U, hU, hUd⟩ := key ![a 1, a 0, a 2] d1 e1 (sq_one_of_natAbs h0)
        (sq_one_of_natAbs h2)
      refine ⟨σ * U, U * σ, σ, σ, ?_, hσ, ?_⟩
      · rw [Matrix.mul_assoc, ← Matrix.mul_assoc U, hU, Matrix.one_mul, hσ]
      · rw [Matrix.mul_assoc σ U, ← hUd]
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [σ, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply, Matrix.vecMul, dotProduct]
  · -- `a 2 = ±p`
    have h0 : (a 0).natAbs = 1 := Nat.eq_one_of_mul_eq_one_right h01
    have h1 : (a 1).natAbs = 1 := Nat.eq_one_of_mul_eq_one_left h01
    have h2' : (a 2).natAbs = p := by
      have := h; rw [h0, h1, one_mul, one_mul] at this; exact this
    obtain ⟨d2, e2⟩ := hdiv _ h2'
    let σ : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
    have hσ : σ * σ = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [σ, Matrix.mul_apply, Fin.sum_univ_three]
    obtain ⟨U, hU, hUd⟩ := key ![a 2, a 1, a 0] d2 e2 (sq_one_of_natAbs h1)
      (sq_one_of_natAbs h0)
    refine ⟨σ * U, U * σ, σ, σ, ?_, hσ, ?_⟩
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc U, hU, Matrix.one_mul, hσ]
    · rw [Matrix.mul_assoc σ U, ← hUd]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [σ, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply, Matrix.vecMul, dotProduct]

theorem gP_val (hp : p.Prime) :
    (gP hp).val = (diagonal ![(p : ℤ), 1, 1]).map (Int.cast : ℤ → ℚ) := by
  change diagonal ![(p : ℚ), 1, 1] = _
  rw [diagonal_map (by simp)]
  congr 1; funext i; fin_cases i <;> simp

theorem intCast_map_mul3 (M N : Matrix (Fin 3) (Fin 3) ℤ) :
    (M * N).map (Int.cast : ℤ → ℚ) = M.map (Int.cast : ℤ → ℚ) * N.map (Int.cast : ℤ → ℚ) := by
  have := Matrix.map_mul (L := M) (M := N) (f := Int.castRingHom ℚ)
  simpa only [Int.coe_castRingHom] using this

theorem intCast_det (M : Matrix (Fin 3) (Fin 3) ℤ) :
    (M.map (Int.cast : ℤ → ℚ)).det = (M.det : ℚ) := by
  have := (Int.castRingHom ℚ).map_det M
  simpa only [Int.coe_castRingHom, RingHom.mapMatrix_apply] using this.symm

theorem natAbs_det_unimodular {M M' : Matrix (Fin 3) (Fin 3) ℤ} (h : M * M' = 1) :
    M.det.natAbs = 1 := by
  have hd : M.det * M'.det = 1 := by rw [← det_mul, h, det_one]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with e | e <;> rw [e] <;> rfl

/-- **The prime double coset.** -/
theorem mem_DZ_gP_iff (hp : p.Prime) (x : RationalGL3) :
    x ∈ DZ (gP hp) ↔
      (∀ i j, ∃ z : ℤ, (z : ℚ) = x.val i j) ∧ (x.val.det = p ∨ x.val.det = -p) := by
  constructor
  · rintro ⟨_, ⟨a₀, rfl⟩, _, ⟨b₀, rfl⟩, rfl⟩
    have hval : (integralRational a₀ * gP hp * integralRational b₀).val =
        (a₀.val * diagonal ![(p : ℤ), 1, 1] * b₀.val).map (Int.cast : ℤ → ℚ) := by
      rw [Units.val_mul, Units.val_mul, gP_val, intCast_map_mul3, intCast_map_mul3]
      rfl
    rw [hval]
    refine ⟨fun i j => ⟨_, rfl⟩, ?_⟩
    rw [intCast_det, det_mul, det_mul, det_diagonal, Fin.prod_univ_three]
    have ha := natAbs_det_unimodular a₀.mul_inv
    have hb := natAbs_det_unimodular b₀.mul_inv
    rcases Int.natAbs_eq a₀.val.det with e1 | e1 <;> rcases Int.natAbs_eq b₀.val.det with e2 | e2 <;>
      rw [e1, e2, ha, hb] <;> simp
  · rintro ⟨hint, hdet⟩
    choose Xf hXf using hint
    let X : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of Xf
    have hX : X.map (Int.cast : ℤ → ℚ) = x.val := by ext i j; exact hXf i j
    have hXdet : X.det.natAbs = p := by
      have h1 : (X.det : ℚ) = x.val.det := by rw [← intCast_det, hX]
      rcases hdet with h | h
      · have : X.det = p := by exact_mod_cast h1.trans h
        rw [this]; rfl
      · have : X.det = -p := by exact_mod_cast h1.trans h
        rw [this]; simp
    have hX0 : X.det ≠ 0 := by
      intro h0; rw [h0] at hXdet; exact hp.ne_zero hXdet.symm
    obtain ⟨A, Q, A', Q', a, hAA, _, hQQ, hQ'Q, hXeq⟩ :=
      HeckeCommutativity.exists_eq_mul_diagonal_mul X hX0
    have hprod : (a 0 * a 1 * a 2).natAbs = p := by
      have := congrArg Matrix.det hXeq
      rw [det_mul, det_mul, det_diagonal, Fin.prod_univ_three] at this
      rw [← hXdet, this, Int.natAbs_mul (A.det * _) Q.det, Int.natAbs_mul A.det,
        natAbs_det_unimodular hAA, natAbs_det_unimodular hQQ, one_mul, mul_one]
    obtain ⟨P, P₁, P', P₁', hP, hP', hdiag⟩ := prime_diagonal hp a hprod
    have h1 : A * P * (P₁ * A') = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hP, Matrix.one_mul, hAA]
    have h2 : P' * Q * (Q' * P₁') = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQQ, Matrix.one_mul, hP']
    refine ⟨integralRational (intUnit _ _ h1), ⟨_, rfl⟩, integralRational (intUnit _ _ h2),
      ⟨_, rfl⟩, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, intUnit_val, intUnit_val, gP_val, ← intCast_map_mul3,
      ← intCast_map_mul3, ← hX, hXeq, hdiag]
    congr 1
    simp only [Matrix.mul_assoc]

theorem plane_val (v : ℚ × ℚ) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    (pU v * planeLevi B s).val =
      !![B.val 0 0, B.val 0 1, v.1 * s; B.val 1 0, B.val 1 1, v.2 * s; 0, 0, (s : ℚ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pU, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

/-- **Plane radical sets of the prime double coset.** -/
theorem plane_mem_DZ_gP_iff (hp : p.Prime) (v : ℚ × ℚ) (B : GeneralLinearGroup (Fin 2) ℚ)
    (s : ℚˣ) :
    pU v * planeLevi B s ∈ DZ (gP hp) ↔
      ((∀ i j, ∃ z : ℤ, (z : ℚ) = B.val i j) ∧ (∃ z : ℤ, (z : ℚ) = s) ∧
        (∃ z : ℤ, (z : ℚ) = v.1 * s) ∧ (∃ z : ℤ, (z : ℚ) = v.2 * s)) ∧
      (B.val.det * s = p ∨ B.val.det * s = -p) := by
  have hdet : (pU v * planeLevi B s).val.det = B.val.det * s := by
    rw [plane_val, det_fin_three, det_fin_two]
    simp
    ring
  rw [mem_DZ_gP_iff, hdet, plane_val]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa using h 0 0
      · simpa using h 0 1
      · simpa using h 1 0
      · simpa using h 1 1
    · simpa using h 2 2
    · simpa using h 0 2
    · simpa using h 1 2
  · rintro ⟨hB, hs, h1, h2⟩ i j
    fin_cases i <;> fin_cases j
    · simpa using hB 0 0
    · simpa using hB 0 1
    · simpa using h1
    · simpa using hB 1 0
    · simpa using hB 1 1
    · simpa using h2
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · simpa using hs

end TernaryPeriodPolynomials.HeckeEigen.Satake
