module

public import TernaryPeriodPolynomials.ModularForm.ModularPeriod.Swap

@[expose] public section


noncomputable section
open MvPolynomial

namespace TernaryPoly.BinaryCuspPeriod

/-- The exponent convention is literally X^j Y^(d-j). -/
theorem monomial_exponent (d j : ℕ) (a : ℂ) :
    monomial (exponent d j) a = C a * X 0 ^ j * X 1 ^ (d-j) := by
  rw [exponent, monomial_add_single, ← C_mul_X_pow_eq_monomial]

/-- Swapping the variables reverses the finite coefficient index. -/
theorem swap_monomial_exponent {d j : ℕ} (hj : j ≤ d) (a : ℂ) :
    bind₁ ![X 1, X 0] (monomial (exponent d j) a) = monomial (exponent d (d-j)) a := by
  simp [monomial_exponent, Nat.sub_sub_self hj]
  ring

/-- Odd powers of X give the literal first-coordinate sign equation. -/
theorem odd_first_monomial {d j : ℕ} (ho : Odd j) (a : ℂ) :
    bind₁ ![-X 0, X 1] (monomial (exponent d j) a) = -monomial (exponent d j) a := by
  simp [monomial_exponent, neg_pow, ho.neg_one_pow]

/-- Odd powers of Y give the literal second-coordinate sign equation. -/
theorem odd_second_monomial {d j : ℕ} (ho : Odd (d-j)) (a : ℂ) :
    bind₁ ![X 0, -X 1] (monomial (exponent d j) a) = -monomial (exponent d j) a := by
  simp [monomial_exponent, neg_pow, ho.neg_one_pow]

/-- Reflection preserves the finite set of odd indices in even degree. -/
theorem reflect_mem_odd_range {d j : ℕ} (hd : Even d)
    (hj : j ∈ (Finset.range (d+1)).filter Odd) :
    d-j ∈ (Finset.range (d+1)).filter Odd := by
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨by omega, Nat.Even.sub_odd (by omega) hd hj.2⟩

/-- The actual Mellin odd-period polynomial is symmetric under swapping X and Y. -/
theorem oddPeriod_swap {d : ℕ} (hd : Even d) (f : Forms d) :
    bind₁ ![X 1, X 0] (oddPeriod f) = oddPeriod f := by
  classical
  rw [oddPeriod, map_sum]
  refine Finset.sum_bij (fun j _ => d-j) ?_ ?_ ?_ ?_
  · intro j hj
    exact reflect_mem_odd_range hd hj
  · intro j hj k hk h
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hk' := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    omega
  · intro j hj
    refine ⟨d-j, reflect_mem_odd_range hd hj, ?_⟩
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    omega
  · intro j hj
    have hj' : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
    rw [swap_monomial_exponent hj', periodCoefficient_reflection hd f hj'
      (Finset.mem_filter.mp hj).2]

/-- Literal separate oddness in the first variable, for the actual finite Mellin polynomial. -/
theorem oddPeriod_odd_first {d : ℕ} (f : Forms d) :
    bind₁ ![-X 0, X 1] (oddPeriod f) = -oddPeriod f := by
  classical
  rw [oddPeriod, map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact odd_first_monomial (Finset.mem_filter.mp hj).2 _

/-- Literal separate oddness in the second variable when the homogeneous degree is even. -/
theorem oddPeriod_odd_second {d : ℕ} (hd : Even d) (f : Forms d) :
    bind₁ ![X 0, -X 1] (oddPeriod f) = -oddPeriod f := by
  classical
  rw [oddPeriod, map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  exact odd_second_monomial (Nat.Even.sub_odd hj' hd (Finset.mem_filter.mp hj).2) _

end TernaryPoly.BinaryCuspPeriod
