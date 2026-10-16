module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Basic
public import TernaryPeriodPolynomials.Polynomial.TaylorHasse
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Module.Rat

@[expose] public section

open Polynomial

noncomputable section
namespace TernaryPoly
variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem eval_todd_monomial_sub (u : R) (n : ℕ) (r : R) :
    (todd u (monomial n r)).eval (-u) - (todd u (monomial n r)).eval 0 =
      if n = 1 then -u * r else 0 := by
  classical
  rw [todd_monomial, eval_finsetSum, eval_finsetSum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, eval_monomial, pow_zero, mul_one, sub_self, add_zero]
  have hterm (k : ℕ) (hk : k ∈ Finset.range n) :
      ((algebraMap ℚ R (_root_.bernoulli k) * (-u)^k) * ((n.choose k : R) * r)) *
          (-u)^(n-k) -
        ((algebraMap ℚ R (_root_.bernoulli k) * (-u)^k) * ((n.choose k : R) * r)) *
          (0:R)^(n-k) =
      ((-u)^n * r) * algebraMap ℚ R ((n.choose k : ℚ) * _root_.bernoulli k) := by
    have hk' : k < n := Finset.mem_range.mp hk
    rw [zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hk')), mul_zero, sub_zero,
      map_mul, map_natCast]
    have hp : (-u)^k * (-u)^(n-k) = (-u)^n := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hk')]
    calc
      _ = ((-u)^k * (-u)^(n-k)) * r *
          ((n.choose k : R) * algebraMap ℚ R (_root_.bernoulli k)) := by ring
      _ = _ := by rw [hp]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum, _root_.sum_bernoulli]
  split_ifs with hn
  · subst n
    simp
  · simp

/-- Translation commutes with the terminating Todd operator. -/
theorem taylor_todd (u v : R) (p : Polynomial R) :
    taylor v (todd u p) = todd u (taylor v p) := by
  rw [todd_eq_sum u p (p.natDegree+1) (Nat.lt_succ_self _),
    todd_eq_sum u (taylor v p) (p.natDegree+1) (by simp),
    map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, hasseDeriv_taylor]

private theorem taylor_todd_difference_monomial (u : R) (n : ℕ) (r : R) :
    taylor (-u) (todd u (monomial n r)) - todd u (monomial n r) =
      (-u) • derivative (monomial n r) := by
  let : IsAddTorsionFree R := IsAddTorsionFree.of_module_rat R
  induction n generalizing r with
  | zero =>
    rw [todd_monomial]
    simp only [Nat.zero_add, Finset.sum_range_one, Nat.sub_self, _root_.bernoulli_zero,
      map_one, pow_zero, Nat.choose_self, Nat.cast_one, one_mul, mul_one,
      monomial_zero_left, taylor_C, derivative_C, sub_self, smul_zero]
  | succ n ih =>
    let q := taylor (-u) (todd u (monomial (n+1) r)) - todd u (monomial (n+1) r) -
      (-u) • derivative (monomial (n+1) r)
    have hd : derivative q = 0 := by
      dsimp [q]
      simp only [map_sub, derivative_taylor, derivative_todd, map_smul,
        derivative_monomial_succ]
      rw [ih]
      simp
    have he : q.eval 0 = 0 := by
      dsimp [q]
      rw [eval_sub, eval_sub, taylor_eval, zero_add, eval_todd_monomial_sub,
        derivative_monomial_succ, eval_smul, eval_monomial]
      cases n <;> simp [smul_eq_mul]
    have hq : q = 0 := by
      rw [eq_C_of_derivative_eq_zero hd, coeff_zero_eq_eval_zero, he, map_zero]
    exact sub_eq_zero.mp hq

/-- The finite Bernoulli operator inverts a finite difference up to `-u ∂`. -/
theorem todd_difference (u : R) (p : Polynomial R) :
    todd u (taylor (-u) p - p) = (-u) • derivative p := by
  rw [map_sub, ← taylor_todd]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, smul_add]
    rw [add_sub_add_comm, hp, hq]
  | monomial n r => exact taylor_todd_difference_monomial u n r

end TernaryPoly
