module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3CosetsPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelThreePairing

@[expose] public section


/-!
# The general Hecke adjointness constant of the parabolic cup pairing

`kappaGen m e e' p = (frickeKappa p m e e' * (-ε_p))⁻¹`.  For `n` odd (`m = n + 1` even,
`(e, e') = (0, -1)`) it equals `p⁻¹`, the level-three constant; for `n` even (`m = n + 1` odd,
`(e, e') = (0, 0)`) it equals `ε_p`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open TernaryPeriodPolynomials.BoundaryDuality

/-- the general adjointness constant -/
noncomputable def kappaGen (m : ℕ) (e e' : ℤ) (p : Nat.Primes) : ℂ :=
  (AdjL3Cosets.frickeKappa p m e e' * (-((AdjL3Cosets.eps p : ℤ) : ℂ)))⁻¹

theorem kappaGen_ne_zero (m : ℕ) (e e' : ℤ) (p : Nat.Primes) : kappaGen m e e' p ≠ 0 := by
  unfold kappaGen
  exact inv_ne_zero (mul_ne_zero (AdjL3Cosets.frickeKappa_ne_zero p m e e')
    (neg_ne_zero.mpr (AdjL3Cosets.eps_ne_zero_C p)))

/-- bad line / good plane, n odd: m = n+1 even, (e,e') = (0,-1): kappa = p⁻¹ -/
theorem kappaGen_odd (n : ℕ) (hn : Odd n) (p : Nat.Primes) :
    kappaGen (n + 1) 0 (-1) p = AdjointLevelThree.levelThreeKappa p := by
  have hE2 : ((AdjL3Cosets.eps p : ℤ) : ℂ) * ((AdjL3Cosets.eps p : ℤ) : ℂ) = 1 := by
    exact_mod_cast AdjL3Cosets.eps_mul_self p
  have hP := AdjL3Cosets.prime_ne_zero_C p
  have hE := AdjL3Cosets.eps_ne_zero_C p
  set E : ℂ := ((AdjL3Cosets.eps p : ℤ) : ℂ) with hEdef
  set P : ℂ := (p.val : ℂ) with hPdef
  have hX : P * E ≠ 0 := mul_ne_zero hP hE
  have hodd : Odd (n + 1 + 1) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k + 1, by omega⟩
  have h1 : (-(P * E)) ^ (((0 : ℤ) + (-1) - ((n + 1 : ℕ) : ℤ))) =
      ((-(P * E)) ^ (n + 1 + 1))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]
    congr 1
    push_cast
    ring
  have h2 : (P * E) ^ (((n + 1 : ℕ) : ℤ) - 2 * (-1)) = (P * E) ^ (n + 1 + 2) := by
    rw [← zpow_natCast]
    congr 1
  have hk : AdjL3Cosets.frickeKappa p (n + 1) 0 (-1) = -(P * E) := by
    unfold AdjL3Cosets.frickeKappa
    rw [h1, h2, hodd.neg_pow]
    have : (P * E) ^ (n + 1 + 1) ≠ 0 := pow_ne_zero _ hX
    field_simp
    ring
  unfold kappaGen AdjointLevelThree.levelThreeKappa
  rw [hk]
  have h3 : -(P * E) * -E = P := by linear_combination P * hE2
  rw [h3]

/-- even n: m = n+1 odd, (e,e') = (0,0): kappa = eps_p (the sign ≡ p mod 3) -/
theorem kappaGen_even (n : ℕ) (hn : Even n) (p : Nat.Primes) :
    kappaGen (n + 1) 0 0 p = ((AdjL3Cosets.eps p : ℤ) : ℂ) := by
  have hE2 : ((AdjL3Cosets.eps p : ℤ) : ℂ) * ((AdjL3Cosets.eps p : ℤ) : ℂ) = 1 := by
    exact_mod_cast AdjL3Cosets.eps_mul_self p
  have hP := AdjL3Cosets.prime_ne_zero_C p
  have hE := AdjL3Cosets.eps_ne_zero_C p
  set E : ℂ := ((AdjL3Cosets.eps p : ℤ) : ℂ) with hEdef
  set P : ℂ := (p.val : ℂ) with hPdef
  have hX : P * E ≠ 0 := mul_ne_zero hP hE
  have hodd : Odd (n + 1) := hn.add_one
  have h1 : (-(P * E)) ^ (((0 : ℤ) + 0 - ((n + 1 : ℕ) : ℤ))) =
      ((-(P * E)) ^ (n + 1))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]
    congr 1
  have h2 : (P * E) ^ (((n + 1 : ℕ) : ℤ) - 2 * 0) = (P * E) ^ (n + 1) := by
    rw [← zpow_natCast]
    congr 1
  have hk : AdjL3Cosets.frickeKappa p (n + 1) 0 0 = -1 := by
    unfold AdjL3Cosets.frickeKappa
    rw [h1, h2, hodd.neg_pow]
    have : (P * E) ^ (n + 1) ≠ 0 := pow_ne_zero _ hX
    field_simp
  unfold kappaGen
  rw [hk]
  field_simp
  linear_combination -hE2

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
