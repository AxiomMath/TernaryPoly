module

public import TernaryPeriodPolynomials.ModularForm.HeckeLSeries.EulerProduct
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryHeckeEulerProduct

/-- Dividing a prime-power recurrence by a geometric weight preserves its exact Euler form. -/
theorem divide_power_recurrence (a : ℕ → ℂ) (b c : ℂ) (hb : b≠0)
    (hr : ∀ r,a (r+2)=a 1*a (r+1)-c*a r) (r : ℕ) :
    a (r+2)/b^(r+2)=(a 1/b)*(a (r+1)/b^(r+1))-(c/b^2)*(a r/b^r) := by
  rw [hr r]
  simp only [pow_add,pow_one,pow_two]
  field_simp [hb]

/-- Actual Mathlib L-series are nonzero at every absolutely convergent natural argument
for normalized multiplicative coefficients satisfying the two-term prime recurrence. -/
theorem LSeries_nat_ne_zero (a : ℕ → ℂ) (c : Nat.Primes → ℂ) (d : ℕ)
    (ha0 : a 0=0) (ha1 : a 1=1)
    (hm : ∀ m n,m.Coprime n → a (m*n)=a m*a n)
    (hr : ∀ p : Nat.Primes, ∀ r : ℕ,
      a (p.val^(r+2))=a p.val*a (p.val^(r+1))-c p*a (p.val^r))
    (hs : LSeriesSummable a (d : ℂ)) : LSeries a (d : ℂ)≠0 := by
  let f : ℕ → ℂ := fun n => a n/(n : ℂ)^d
  have ht : LSeries.term a (d : ℂ)=f := by
    funext n
    by_cases hn : n=0
    · subst n
      simp [LSeries.term_def,f,ha0]
    · simp [hn,Complex.cpow_natCast,f]
  change Summable (LSeries.term a (d : ℂ)) at hs
  rw [ht] at hs
  change (∑' n,LSeries.term a (d : ℂ) n)≠0
  rw [ht]
  apply multiplicative_tsum_ne_zero f (fun p => c p/((p.val : ℂ)^d)^2)
  · simp [f,ha0]
  · simp [f,ha1]
  · intro m n hmn
    simp only [f,Nat.cast_mul,mul_pow,hm m n hmn,mul_div_mul_comm]
  · intro p r
    have hb : (p.val : ℂ)^d≠0 := pow_ne_zero _ (by
      exact_mod_cast (Nat.Prime.ne_zero ((Nat.irreducible_iff_nat_prime _).mp p.property)))
    have hp (r : ℕ) : f (p.val^r)=a (p.val^r)/((p.val : ℂ)^d)^r := by
      dsimp only [f]
      rw [Nat.cast_pow,←pow_mul,Nat.mul_comm,pow_mul]
    simp only [hp]
    have he := divide_power_recurrence (fun r => a (p.val^r)) ((p.val : ℂ)^d) (c p) hb
      (by simpa only [pow_one] using hr p) r
    simpa only [pow_one,f] using he
  · exact summable_norm_iff.mpr hs

end TernaryPoly.BinaryHeckeEulerProduct
