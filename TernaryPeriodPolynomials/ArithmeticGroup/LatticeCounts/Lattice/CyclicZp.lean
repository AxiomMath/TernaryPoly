module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.PermZp
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.HermiteCount

@[expose] public section


/-!
# Cyclic Hermite triples are preserved by `GL₂(ℤ_q)`

Formalized by Claude Haiku 5.5.

A Hermite triple `t` of index `q^r` is cyclic when `gcd(a, b, d) = 1` (`HermiteCount.cyclicHNF`).
For a prime `q` this says that not all of `a, b, d` are divisible by `q`. The `ℤ_q`-matrix
`Mz t` has all its entries in the ideal `(q)` exactly when `q` divides `a`, `b` and `d`, and
multiplying by `ℤ_q`-unit matrices on either side preserves this. Hence the permutation `σ` of
`LatticePermZp.exists_perm_zp` preserves cyclicity (`cyclic_preserved_of_perm`).
-/

open PadicInt Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeCyclicZp

open TernaryPeriodPolynomials.Argument.LatticeCounts
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp

variable {q : ℕ} [Fact q.Prime]

/-- For a natural number `n`, `(n : ℤ_q)` lies in `(q)` exactly when `q ∣ n`. -/
theorem natCast_mem_span_iff (n : ℕ) : (n : ℤ_[q]) ∈ Ideal.span {(q : ℤ_[q])} ↔ q ∣ n := by
  have h : Ideal.span {(q : ℤ_[q])} = RingHom.ker (PadicInt.toZModPow (p := q) 1) := by
    rw [PadicInt.ker_toZModPow, pow_one]
  rw [h, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff, pow_one]

/-- For `a * d = q^r`, `gcd(a, b, d) = 1` iff not all of `a, b, d` are divisible by the prime `q`. -/
theorem gcd_eq_one_iff_not_dvd {q : ℕ} (hq : q.Prime) {a b d r : ℕ} (h : a * d = q ^ r) :
    Nat.gcd (Nat.gcd a b) d = 1 ↔ ¬ (q ∣ a ∧ q ∣ b ∧ q ∣ d) := by
  have had : a ∣ q ^ r := by rw [← h]; exact Dvd.intro d rfl
  have hga : Nat.gcd (Nat.gcd a b) d ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgb : Nat.gcd (Nat.gcd a b) d ∣ b := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgd : Nat.gcd (Nat.gcd a b) d ∣ d := Nat.gcd_dvd_right _ _
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hq).1 (hga.trans had)
  constructor
  · rintro h1 ⟨ha, hb, hd⟩
    have hqg : q ∣ Nat.gcd (Nat.gcd a b) d := Nat.dvd_gcd (Nat.dvd_gcd ha hb) hd
    rw [h1] at hqg
    exact hq.one_lt.ne' (Nat.dvd_one.1 hqg)
  · intro hnot
    by_contra h1
    have hm0 : m ≠ 0 := fun h0 => h1 (by rw [hm, h0, pow_zero])
    have hqg : q ∣ Nat.gcd (Nat.gcd a b) d := by
      rw [hm]
      exact dvd_pow_self q hm0
    exact hnot ⟨hqg.trans hga, hqg.trans hgb, hqg.trans hgd⟩

theorem mul_left_mem_entries {I : Ideal ℤ_[q]} (Y M : Matrix (Fin 2) (Fin 2) ℤ_[q])
    (hM : ∀ i j, M i j ∈ I) : ∀ i j, (Y * M) i j ∈ I := by
  intro i j
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hM k j)

theorem mul_right_mem_entries {I : Ideal ℤ_[q]} (M C : Matrix (Fin 2) (Fin 2) ℤ_[q])
    (hM : ∀ i j, M i j ∈ I) : ∀ i j, (M * C) i j ∈ I := by
  intro i j
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (hM i k)

/-- If `Y * M = N * C` with `C` a unit and `Y` a unit determinant, the entries of `M` lie in `I`
iff those of `N` do. -/
theorem entries_mem_iff_of_perm {I : Ideal ℤ_[q]} {Y N M : Matrix (Fin 2) (Fin 2) ℤ_[q]}
    (hY : IsUnit Y.det) {C : (Matrix (Fin 2) (Fin 2) ℤ_[q])ˣ} (h : Y * M = N * C.val) :
    (∀ i j, M i j ∈ I) ↔ (∀ i j, N i j ∈ I) := by
  constructor
  · intro hM
    have h1 := mul_left_mem_entries (I := I) Y M hM
    rw [h] at h1
    have h2 := mul_right_mem_entries _ (C⁻¹ : (Matrix (Fin 2) (Fin 2) ℤ_[q])ˣ).val h1
    have hN : N * C.val * (C⁻¹ : (Matrix (Fin 2) (Fin 2) ℤ_[q])ˣ).val = N := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [hN] at h2
    exact h2
  · intro hN
    have h1 := mul_right_mem_entries N C.val hN
    rw [← h] at h1
    have h2 := mul_left_mem_entries (I := I) Y⁻¹ (Y * M) h1
    have hM : Y⁻¹ * (Y * M) = M := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hY, Matrix.one_mul]
    rw [hM] at h2
    exact h2

/-- A Hermite triple of level `q^r` is cyclic iff not all entries of its `ℤ_q`-matrix lie in `(q)`. -/
theorem mem_cyclicHNF_iff {r : ℕ} (hq : q.Prime) (t : ℕ × ℕ × ℕ) (ht : t ∈ hnfData (q ^ r)) :
    t ∈ cyclicHNF q r ↔ ¬ ∀ i j, Mz (q := q) t i j ∈ Ideal.span {(q : ℤ_[q])} := by
  have hn : 0 < q ^ r := pow_pos hq.pos r
  obtain ⟨-, h2, -⟩ := (mem_hnfData hn t).1 ht
  have hall : (∀ i j, Mz (q := q) t i j ∈ Ideal.span {(q : ℤ_[q])}) ↔
      ((t.1 : ℤ_[q]) ∈ Ideal.span {(q : ℤ_[q])} ∧ (t.2.1 : ℤ_[q]) ∈ Ideal.span {(q : ℤ_[q])} ∧
        (t.2.2 : ℤ_[q]) ∈ Ideal.span {(q : ℤ_[q])}) := by
    constructor
    · intro H
      exact ⟨by simpa [Mz] using H 0 0, by simpa [Mz] using H 1 0, by simpa [Mz] using H 1 1⟩
    · rintro ⟨A, B, D⟩ i j
      fin_cases i <;> fin_cases j <;> simp [Mz, A, B, D]
  rw [hall, natCast_mem_span_iff, natCast_mem_span_iff, natCast_mem_span_iff]
  unfold cyclicHNF
  rw [Finset.mem_filter, and_iff_right ht, gcd_eq_one_iff_not_dvd hq h2]

/-- The permutation of `exists_perm_zp` preserves cyclicity of Hermite triples. -/
theorem cyclic_preserved_of_perm {r : ℕ} (hq : q.Prime) (Y : Matrix (Fin 2) (Fin 2) ℤ_[q])
    (hY : IsUnit Y.det)
    (σ : {t // t ∈ hnfData (q ^ r)} ≃ {t // t ∈ hnfData (q ^ r)})
    (hσ : ∀ t : {t // t ∈ hnfData (q ^ r)}, ∃ C : (Matrix (Fin 2) (Fin 2) ℤ_[q])ˣ,
      Y * Mz t.1 = Mz (σ t).1 * C.val) :
    ∀ t : {t // t ∈ hnfData (q ^ r)}, t.1 ∈ cyclicHNF q r ↔ (σ t).1 ∈ cyclicHNF q r := by
  intro t
  obtain ⟨C, hC⟩ := hσ t
  rw [mem_cyclicHNF_iff hq t.1 t.2, mem_cyclicHNF_iff hq (σ t).1 (σ t).2]
  exact not_congr (entries_mem_iff_of_perm hY hC)

end TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeCyclicZp

end
