module

public import Mathlib
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.HNF

@[expose] public section


/-!
# Cyclic sublattices of `ℤ²` of finite index

Formalized by Claude Haiku 5.5.
Paper: Appendix C.

For a Hermite triple `(a, b, d)` with `d > 0`, the quotient `ℤ² / latZ a b d` is cyclic exactly when
`gcd(a, b, d) = 1`.
-/

namespace TernaryPeriodPolynomials.Argument.LatticeCounts

/-- `gcd(a, b, d) = 1` exactly when no prime divides all three. -/
theorem gcd_eq_one_iff_prime (a b d : ℕ) :
    Nat.gcd (Nat.gcd a b) d = 1 ↔ ∀ q : ℕ, q.Prime → ¬ (q ∣ a ∧ q ∣ b ∧ q ∣ d) := by
  constructor
  · rintro h q hq ⟨h1, h2, h3⟩
    have hdvd : q ∣ Nat.gcd (Nat.gcd a b) d := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3
    rw [h] at hdvd
    exact hq.not_dvd_one hdvd
  · intro h
    by_contra hne
    have hq : (Nat.gcd (Nat.gcd a b) d).minFac.Prime := Nat.minFac_prime hne
    have hqg : (Nat.gcd (Nat.gcd a b) d).minFac ∣ Nat.gcd (Nat.gcd a b) d := Nat.minFac_dvd _
    exact h _ hq ⟨(hqg.trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_left a b),
      (hqg.trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_right a b),
      hqg.trans (Nat.gcd_dvd_right _ d)⟩

/-- Integer form of the prime condition, for the cast triple. -/
theorem cond_int_of_gcd {a b d : ℕ} (h : Nat.gcd (Nat.gcd a b) d = 1) :
    ∀ q : ℕ, q.Prime → ¬ ((q : ℤ) ∣ (a : ℤ) ∧ (q : ℤ) ∣ (b : ℤ) ∧ (q : ℤ) ∣ (d : ℤ)) := by
  rintro q hq ⟨h1, h2, h3⟩
  exact (gcd_eq_one_iff_prime a b d).1 h q hq
    ⟨Int.natCast_dvd_natCast.mp h1, Int.natCast_dvd_natCast.mp h2, Int.natCast_dvd_natCast.mp h3⟩

/-- Affine coprimality: if no prime divides `a`, `b` and `d` together, then `b - a y` is coprime to `d`
for some integer `y`. -/
theorem exists_isCoprime_affine (a b : ℤ) (d : ℕ) (hd : 0 < d)
    (hcond : ∀ q : ℕ, q.Prime → ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b ∧ (q : ℤ) ∣ (d : ℤ))) :
    ∃ y : ℤ, IsCoprime (b - a * y) (d : ℤ) := by
  revert hd hcond
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp0 hn0 =>
    intro _ hc
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp0
    have hirr : Irreducible (p : ℤ) := hpZ.irreducible
    push_cast at hc ⊢
    by_cases hpa : (p : ℤ) ∣ a
    · have hpb : ¬ (p : ℤ) ∣ b := fun h => hc p hp0 ⟨hpa, h, dvd_pow_self _ hn0.ne'⟩
      refine ⟨0, ?_⟩
      rw [mul_zero, sub_zero]
      exact IsCoprime.pow_right ((hirr.coprime_iff_not_dvd.2 hpb).symm)
    · obtain ⟨s, t, hst⟩ := (hirr.coprime_iff_not_dvd.2 hpa).symm
      refine ⟨s * (b + 1), ?_⟩
      have e : b - a * (s * (b + 1)) = -1 + (p : ℤ) * (t * (b + 1)) := by
        linear_combination (-(b + 1)) * hst
      rw [e]
      have hc1 : IsCoprime (-1 + (p : ℤ) * (t * (b + 1))) (p : ℤ) :=
        ⟨-1, t * (b + 1), by ring⟩
      exact hc1.pow_right
  | zero =>
    intro h
    exact absurd h (lt_irrefl 0)
  | one =>
    intro _ _
    exact ⟨0, by simp [isCoprime_one_right]⟩
  | coprime m n hm hn hmn ihm ihn =>
    intro _ hc
    have hm0 : 0 < m := by omega
    have hn0 : 0 < n := by omega
    have hcm : ∀ q : ℕ, q.Prime → ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b ∧ (q : ℤ) ∣ (m : ℤ)) :=
      fun q hq h => hc q hq ⟨h.1, h.2.1, by rw [Nat.cast_mul]; exact dvd_mul_of_dvd_left h.2.2 _⟩
    have hcn : ∀ q : ℕ, q.Prime → ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b ∧ (q : ℤ) ∣ (n : ℤ)) :=
      fun q hq h => hc q hq ⟨h.1, h.2.1, by rw [Nat.cast_mul]; exact dvd_mul_of_dvd_right h.2.2 _⟩
    obtain ⟨y1, hy1⟩ := ihm hm0 hcm
    obtain ⟨y2, hy2⟩ := ihn hn0 hcn
    obtain ⟨s, t, hst⟩ := (Nat.isCoprime_iff_coprime.mpr hmn : IsCoprime (m : ℤ) (n : ℤ))
    refine ⟨y1 * (t * n) + y2 * (s * m), ?_⟩
    have ey1 : b - a * (y1 * (t * (n : ℤ)) + y2 * (s * (m : ℤ)))
        = (b - a * y1) + (m : ℤ) * (-(a * s * (y2 - y1))) := by
      linear_combination (-(a * y1)) * hst
    have ey2 : b - a * (y1 * (t * (n : ℤ)) + y2 * (s * (m : ℤ)))
        = (b - a * y2) + (n : ℤ) * (-(a * t * (y1 - y2))) := by
      linear_combination (-(a * y2)) * hst
    have hcopM : IsCoprime (b - a * (y1 * (t * (n : ℤ)) + y2 * (s * (m : ℤ)))) (m : ℤ) := by
      rw [ey1]
      obtain ⟨u, v, huv⟩ := hy1
      exact ⟨u, v - u * (-(a * s * (y2 - y1))), by linear_combination huv⟩
    have hcopN : IsCoprime (b - a * (y1 * (t * (n : ℤ)) + y2 * (s * (m : ℤ)))) (n : ℤ) := by
      rw [ey2]
      obtain ⟨u, v, huv⟩ := hy2
      exact ⟨u, v - u * (-(a * t * (y1 - y2))), by linear_combination huv⟩
    rw [Nat.cast_mul]
    exact IsCoprime.mul_right hcopM hcopN

/-- Points of `latZ a b d` are divisible by any common divisor `q` of `a`, `b`, `d`. -/
theorem dvd_of_mem_latZ {a b d q : ℤ} (ha : q ∣ a) (hb : q ∣ b) (hd : q ∣ d) {w : ℤ × ℤ}
    (hw : w ∈ latZ a b d) : q ∣ w.1 ∧ q ∣ w.2 := by
  obtain ⟨m, j, h1, h2⟩ := (mem_latZ w).mp hw
  refine ⟨?_, ?_⟩
  · rw [h1]; exact dvd_mul_of_dvd_right ha m
  · rw [h2]; exact dvd_add (dvd_mul_of_dvd_right hb m) (dvd_mul_of_dvd_right hd j)

/-- Scalar multiplication on pairs. -/
theorem smul_pair_int (k x y : ℤ) : k • ((x, y) : ℤ × ℤ) = (k * x, k * y) := by
  ext <;> simp

/-- `k • mk w = mk (k • w)` in a quotient by an additive subgroup. -/
theorem mk_zsmul_quot (L : AddSubgroup (ℤ × ℤ)) (k : ℤ) (w : ℤ × ℤ) :
    k • (QuotientAddGroup.mk w : (ℤ × ℤ) ⧸ L) = QuotientAddGroup.mk (k • w) :=
  (map_zsmul (QuotientAddGroup.mk' L) k w).symm

/-- A cyclic quotient forces `gcd(a, b, d) = 1`. -/
theorem gcd_eq_one_of_isAddCyclic {a b d : ℕ}
    (hc : IsAddCyclic ((ℤ × ℤ) ⧸ latZ (a : ℤ) (b : ℤ) (d : ℤ))) :
    Nat.gcd (Nat.gcd a b) d = 1 := by
  rw [gcd_eq_one_iff_prime]
  rintro q hq ⟨hqa, hqb, hqd⟩
  have hqa' : ((q : ℕ) : ℤ) ∣ (a : ℤ) := Int.natCast_dvd_natCast.mpr hqa
  have hqb' : ((q : ℕ) : ℤ) ∣ (b : ℤ) := Int.natCast_dvd_natCast.mpr hqb
  have hqd' : ((q : ℕ) : ℤ) ∣ (d : ℤ) := Int.natCast_dvd_natCast.mpr hqd
  obtain ⟨g, hg⟩ := (IsAddCyclic.exists_zsmul_surjective :
    ∃ g : (ℤ × ℤ) ⧸ latZ (a : ℤ) (b : ℤ) (d : ℤ), Function.Surjective (fun n : ℤ => n • g))
  obtain ⟨⟨A, B⟩, rfl⟩ := QuotientAddGroup.mk_surjective g
  obtain ⟨k, hk⟩ := hg (QuotientAddGroup.mk ((1 : ℤ), (0 : ℤ)))
  obtain ⟨k', hk'⟩ := hg (QuotientAddGroup.mk ((0 : ℤ), (1 : ℤ)))
  have hk1 : k • (QuotientAddGroup.mk ((A, B) : ℤ × ℤ) : (ℤ × ℤ) ⧸ latZ (a : ℤ) (b : ℤ) (d : ℤ))
      = QuotientAddGroup.mk ((1 : ℤ), (0 : ℤ)) := hk
  have hk2 : k' • (QuotientAddGroup.mk ((A, B) : ℤ × ℤ) : (ℤ × ℤ) ⧸ latZ (a : ℤ) (b : ℤ) (d : ℤ))
      = QuotientAddGroup.mk ((0 : ℤ), (1 : ℤ)) := hk'
  have m1 : (-(k • ((A, B) : ℤ × ℤ)) + ((1 : ℤ), (0 : ℤ))) ∈ latZ (a : ℤ) (b : ℤ) (d : ℤ) :=
    QuotientAddGroup.eq.mp ((mk_zsmul_quot _ k _).symm.trans hk1)
  have m2 : (-(k' • ((A, B) : ℤ × ℤ)) + ((0 : ℤ), (1 : ℤ))) ∈ latZ (a : ℤ) (b : ℤ) (d : ℤ) :=
    QuotientAddGroup.eq.mp ((mk_zsmul_quot _ k' _).symm.trans hk2)
  obtain ⟨hA1, -⟩ := dvd_of_mem_latZ hqa' hqb' hqd' m1
  obtain ⟨hA2, hB2⟩ := dvd_of_mem_latZ hqa' hqb' hqd' m2
  have c1 : (-(k • ((A, B) : ℤ × ℤ)) + ((1 : ℤ), (0 : ℤ))).1 = -(k * A) + 1 := by
    rw [smul_pair_int]; simp
  have c2 : (-(k' • ((A, B) : ℤ × ℤ)) + ((0 : ℤ), (1 : ℤ))).1 = -(k' * A) := by
    rw [smul_pair_int]; simp
  have c3 : (-(k' • ((A, B) : ℤ × ℤ)) + ((0 : ℤ), (1 : ℤ))).2 = -(k' * B) + 1 := by
    rw [smul_pair_int]; simp
  rw [c1] at hA1
  rw [c2] at hA2
  rw [c3] at hB2
  have hkd : ((q : ℕ) : ℤ) ∣ k' := by
    have h := dvd_sub (dvd_mul_of_dvd_right hA1 k') (dvd_mul_of_dvd_right hA2 k)
    have e : k' * (-(k * A) + 1) - k * (-(k' * A)) = k' := by ring
    rwa [e] at h
  have h1 : ((q : ℕ) : ℤ) ∣ 1 := by
    have h := dvd_add hB2 (dvd_mul_of_dvd_left hkd B)
    have e : (-(k' * B) + 1) + k' * B = 1 := by ring
    rwa [e] at h
  have hle : ((q : ℕ) : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
  have := hq.two_le
  omega

/-- A cyclic-generator criterion: if `gcd(a, b, d) = 1` then the quotient is cyclic. -/
theorem isAddCyclic_of_gcd_eq_one {a b d : ℕ} (hd : 0 < d)
    (hg : Nat.gcd (Nat.gcd a b) d = 1) :
    IsAddCyclic ((ℤ × ℤ) ⧸ latZ (a : ℤ) (b : ℤ) (d : ℤ)) := by
  obtain ⟨y, u, v, huv⟩ : ∃ y u v : ℤ, u * ((b : ℤ) - (a : ℤ) * y) + v * (d : ℤ) = 1 := by
    obtain ⟨y, hy⟩ := exists_isCoprime_affine (a : ℤ) (b : ℤ) d hd (cond_int_of_gcd hg)
    obtain ⟨u, v, huv⟩ := hy
    exact ⟨y, u, v, huv⟩
  have hsurj : Function.Surjective (fun n : ℤ =>
      n • (QuotientAddGroup.mk ((1 : ℤ), y) : (ℤ × ℤ) ⧸ latZ (a : ℤ) (b : ℤ) (d : ℤ))) := by
    intro w
    obtain ⟨⟨x, z⟩, rfl⟩ := QuotientAddGroup.mk_surjective w
    refine ⟨x - (z - x * y) * u * (a : ℤ), ?_⟩
    show (x - (z - x * y) * u * (a : ℤ)) • (QuotientAddGroup.mk ((1 : ℤ), y) :
      (ℤ × ℤ) ⧸ latZ (a : ℤ) (b : ℤ) (d : ℤ)) = QuotientAddGroup.mk (x, z)
    rw [mk_zsmul_quot, QuotientAddGroup.eq, mem_latZ, smul_pair_int]
    refine ⟨(z - x * y) * u, (z - x * y) * v, ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.fst_neg]
      ring
    · simp only [Prod.snd_add, Prod.snd_neg]
      linear_combination (-(z - x * y)) * huv
  exact ⟨⟨_, hsurj⟩⟩

/-- For `d > 0`: the quotient `ℤ² / latZ a b d` is cyclic iff `gcd(a, b, d) = 1`. -/
theorem isAddCyclic_quot_latZ_iff {a b d : ℕ} (hd : 0 < d) :
    IsAddCyclic ((ℤ × ℤ) ⧸ latZ (a : ℤ) (b : ℤ) (d : ℤ)) ↔ Nat.gcd (Nat.gcd a b) d = 1 :=
  ⟨gcd_eq_one_of_isAddCyclic, fun h => isAddCyclic_of_gcd_eq_one hd h⟩

/-- The same statement for the sublattice attached to a Hermite triple. -/
theorem isAddCyclic_quot_latOf_iff {t : ℕ × ℕ × ℕ} (ht : 0 < t.2.2) :
    IsAddCyclic ((ℤ × ℤ) ⧸ latOf t) ↔ Nat.gcd (Nat.gcd t.1 t.2.1) t.2.2 = 1 :=
  isAddCyclic_quot_latZ_iff ht

end TernaryPeriodPolynomials.Argument.LatticeCounts
