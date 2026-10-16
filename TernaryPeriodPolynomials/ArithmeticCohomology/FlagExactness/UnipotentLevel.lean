module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Rational square-zero unipotents scaled into the finite level

For a rational `3×3` matrix `N` with `N * N = 0` there is a positive integer `M`
such that every finite-adelic unipotent `1 + (M z) N` with `z ∈ Ẑ` lies in
`finiteLevel`. Concretely, `M = 3·D` where `D` clears all denominators of `N`.

This gives the lattice invariance needed for real constant terms at rational flags.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- The unipotent unit `1 + N` of a square-zero matrix. -/
def unipotentUnit {R : Type*} [CommRing R] (N : Matrix (Fin 3) (Fin 3) R) (h : N * N = 0) :
    GeneralLinearGroup (Fin 3) R :=
  ⟨1 + N, 1 - N, by rw [add_mul, one_mul, mul_sub, mul_one, h, sub_zero, sub_add_cancel],
    by rw [sub_mul, one_mul, mul_add, mul_one, h, add_zero, add_sub_cancel_right]⟩

@[simp] theorem unipotentUnit_val {R : Type*} [CommRing R] (N : Matrix (Fin 3) (Fin 3) R)
    (h : N * N = 0) : (unipotentUnit N h).val = 1 + N := rfl

/-- A common denominator for the entries of a rational matrix. -/
theorem exists_common_denominator (N : Matrix (Fin 3) (Fin 3) ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ i j, ∃ b : ℤ, (D : ℚ) * N i j = b := by
  classical
  refine ⟨∏ p : Fin 3 × Fin 3, (N p.1 p.2).den, ?_, ?_⟩
  · exact Finset.prod_pos (fun p _ => (N p.1 p.2).den_pos)
  · intro i j
    have hdvd : (N i j).den ∣ ∏ p : Fin 3 × Fin 3, (N p.1 p.2).den :=
      Finset.dvd_prod_of_mem (fun p : Fin 3 × Fin 3 => (N p.1 p.2).den) (Finset.mem_univ (i, j))
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨(k : ℤ) * (N i j).num, ?_⟩
    rw [hk]
    push_cast
    rw [mul_comm ((N i j).den : ℚ) (k : ℚ), mul_assoc, mul_comm ((N i j).den : ℚ), Rat.mul_den_eq_num]

theorem scaled_unipotent_mem_finiteLevel (N : Matrix (Fin 3) (Fin 3) ℚ) (hN : N * N = 0) :
    ∃ M : ℕ, 0 < M ∧ ∀ z : IntegralAdeles,
      ∀ h : (((M : FiniteAdeles) * integralEmbedding z) • N.map (algebraMap ℚ FiniteAdeles)) *
          (((M : FiniteAdeles) * integralEmbedding z) • N.map (algebraMap ℚ FiniteAdeles)) = 0,
      unipotentUnit _ h ∈ finiteLevel := by
  obtain ⟨D, hD, hint⟩ := exists_common_denominator N
  choose B hB using hint
  refine ⟨3 * D, by omega, ?_⟩
  intro z h
  -- the integral square-zero matrix
  let Bint : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j => B i j
  have hBint : Bint * Bint = 0 := by
    have hq : (Bint.map (Int.castRingHom ℚ)) * (Bint.map (Int.castRingHom ℚ)) = 0 := by
      have heq : Bint.map (Int.castRingHom ℚ) = (D : ℚ) • N := by
        ext i j
        simp [Bint, Matrix.of_apply, hB]
      rw [heq, smul_mul_smul_comm, hN, smul_zero]
    ext i j
    have := congrFun (congrFun hq i) j
    rw [← Matrix.map_mul, Matrix.map_apply] at this
    simpa using this
  let C : Matrix (Fin 3) (Fin 3) IntegralAdeles :=
    ((3 : IntegralAdeles) * z) • Bint.map (Int.castRingHom IntegralAdeles)
  have hC : C * C = 0 := by
    change (((3 : IntegralAdeles) * z) • Bint.map (Int.castRingHom IntegralAdeles)) *
      (((3 : IntegralAdeles) * z) • Bint.map (Int.castRingHom IntegralAdeles)) = 0
    rw [smul_mul_smul_comm, ← Matrix.map_mul, hBint, Matrix.map_zero _ (map_zero _), smul_zero]
  refine ⟨unipotentUnit C hC, ?_, ?_⟩
  · -- reduction modulo three is the identity
    change GeneralLinearGroup.map integralReduction (unipotentUnit C hC) ∈ rowStabilizer
    have hone : GeneralLinearGroup.map integralReduction (unipotentUnit C hC) = 1 := by
      apply Units.ext
      ext i j
      have h3 : integralReduction (3 : IntegralAdeles) = 0 := by
        rw [map_ofNat]; rfl
      simp [C, Matrix.GeneralLinearGroup.map_apply, h3]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [hone]
    exact rowStabilizer.one_mem
  · apply Units.ext
    apply Matrix.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp only [unipotentUnit_val, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, C, Bint,
      Matrix.of_apply, smul_eq_mul]
    rw [map_add, map_mul, map_mul]
    congr 1
    · rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · have hb : (algebraMap ℚ FiniteAdeles) ((D : ℚ) * N i j) = ((B i j : ℤ) : FiniteAdeles) := by
        rw [hB]; simp
      rw [map_mul, map_natCast] at hb
      rw [Int.coe_castRingHom, integralEmbedding_int, ← hb, map_ofNat]
      push_cast
      ring

end TernaryPeriodPolynomials.FlagExactness
