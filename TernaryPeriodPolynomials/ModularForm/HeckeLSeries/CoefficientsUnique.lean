module

public import TernaryPeriodPolynomials.ModularForm.HeckeLSeries.Coefficients

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryHeckeCoefficients

/-- With fixed prime eigenvalues, zero constant and first coefficients force every coefficient
of a Hecke eigen-sequence to vanish. -/
theorem all_zero_of_first_zero (a : ℕ → ℂ) (c ev : Nat.Primes → ℂ)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (h : ∀ p : Nat.Primes, ∀ n : ℕ,
      a (p.val*n) + c p * (if p.val ∣ n then a (n/p.val) else 0) = ev p * a n) :
    ∀ n, a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · simpa [hn0] using ha0
      by_cases hn1 : n = 1
      · simpa [hn1] using ha1
      obtain ⟨p, hp, k, rfl⟩ := Nat.exists_prime_and_dvd hn1
      have hkpos : 0 < k := by
        by_contra hle
        have : k = 0 := by omega
        simp [this] at hn0
      have hklt : k < p*k := by nlinarith [hp.two_le]
      let pp : Nat.Primes := ⟨p, (Nat.irreducible_iff_nat_prime _).mpr hp⟩
      have he := h pp k
      change a (p*k) + c pp * (if p ∣ k then a (k/p) else 0) = ev pp * a k at he
      rw [ih k hklt] at he
      by_cases hpk : p ∣ k
      · rw [ite_eq_left hpk, ih (k/p) (lt_of_le_of_lt (Nat.div_le_self k p) hklt)] at he
        simpa using he
      · simpa [hpk] using he

end TernaryPoly.BinaryHeckeCoefficients
