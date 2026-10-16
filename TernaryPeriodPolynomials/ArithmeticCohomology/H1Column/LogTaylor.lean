module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantAlgebra
public import TernaryPeriodPolynomials.Polynomial.GLAction
public import Mathlib.RingTheory.Nilpotent.Exp

@[expose] public section


/-!
# `log ρ(U_ij) = -x_j ∂_{x_i}`: the Taylor formula (MR-8)

Formalized by Claude Sonnet 5.5.

`lieOp i j = -x_j ∂_{x_i}` on `ℚ[x_1, x_2, x_3]`.  For `i ≠ j` the shear `x_i ↦ x_i - x_j` (the inverse substitution by `U_ij`) is, on every polynomial of `x_i`-degree below `N`, the truncated exponential
`∑_{k<N} (lieOp i j)^k / k!` (`shear_eq_sum`), and `lieOp i j` is nilpotent on such polynomials (`lieOp_pow_monomial_eq_zero`).
-/

open MvPolynomial Finset

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open TernaryPoly.RadicalCoinvariantAlgebra (shear shear_X)

abbrev Poly := MvPolynomial (Fin 3) ℚ

/-- The Lie algebra operator `-x_j ∂_{x_i}` on polynomials. -/
def lieOp (i j : Fin 3) : Module.End ℚ Poly :=
  LinearMap.mulLeft ℚ (-(X j : Poly)) ∘ₗ (pderiv i).toLinearMap

theorem lieOp_apply (i j : Fin 3) (f : Poly) : lieOp i j f = -X j * pderiv i f := rfl

variable {i j : Fin 3}

/-- A monomial with the `x_i`-exponent removed is killed by `∂_{x_i}`. -/
theorem pderiv_monomial_erase (s : Fin 3 →₀ ℕ) (c : ℚ) : pderiv i (monomial (s.erase i) c) = 0 := by
  rw [pderiv_monomial]
  simp

/-- ... and fixed by the shear. -/
theorem shear_monomial_erase (hij : i ≠ j) (s : Fin 3 →₀ ℕ) (c : ℚ) :
    shear i j (monomial (s.erase i) c) = monomial (s.erase i) c := by
  rw [monomial_eq, map_mul]
  unfold Finsupp.prod
  rw [map_prod]
  simp only [map_pow]
  have h1 : shear i j (C c) = C c := by simp
  rw [h1]
  congr 1
  refine Finset.prod_congr rfl fun n hn => ?_
  have hni : n ≠ i := (Finsupp.mem_support_iff.mp hn |> fun h => by
    intro e; subst e; simp at h)
  simp [shear_X, hni]

theorem monomial_eq_erase_mul (s : Fin 3 →₀ ℕ) (c : ℚ) :
    monomial s c = monomial (s.erase i) c * X i ^ (s i) := by
  rw [← monomial_add_single, Finsupp.erase_add_single]

theorem lieOp_mul_X_pow (hij : i ≠ j) (r : Poly) (hr : pderiv i r = 0) (m k : ℕ) :
    lieOp i j (r * (-X j) ^ k * X i ^ m) = r * (-X j) ^ (k + 1) * ((m : Poly) * X i ^ (m - 1)) := by
  rw [lieOp_apply]
  have hX : pderiv i (X j : Poly) = 0 := pderiv_X_of_ne (Ne.symm hij)
  have hneg : pderiv i (-(X j : Poly)) = 0 := by simp [hX]
  rw [pderiv_mul, pderiv_mul, pderiv_pow, pderiv_pow, hr, hneg, pderiv_X_self]
  simp only [zero_mul, zero_add, mul_zero, add_zero, mul_one]
  ring

/-- Closed form of the powers of `-x_j ∂_{x_i}` on `r · x_i^m`. -/
theorem lieOp_pow_apply (hij : i ≠ j) (r : Poly) (hr : pderiv i r = 0) (m k : ℕ) :
    (lieOp i j ^ k) (r * X i ^ m) = r * (-X j) ^ k * ((m.descFactorial k : Poly) * X i ^ (m - k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hd : pderiv i (r * (m.descFactorial k : Poly)) = 0 := by
      rw [pderiv_mul, hr, Derivation.map_natCast]; simp
    have h := lieOp_mul_X_pow hij (r * (m.descFactorial k : Poly)) hd (m - k) k
    rw [pow_succ', Module.End.mul_apply, ih]
    have e : r * (-X j) ^ k * ((m.descFactorial k : Poly) * X i ^ (m - k)) =
        r * (m.descFactorial k : Poly) * (-X j) ^ k * X i ^ (m - k) := by ring
    rw [e, h, Nat.descFactorial_succ, show m - (k + 1) = m - k - 1 by omega]
    push_cast
    ring

theorem lieOp_pow_monomial (hij : i ≠ j) (s : Fin 3 →₀ ℕ) (c : ℚ) (k : ℕ) :
    (lieOp i j ^ k) (monomial s c) =
      monomial (s.erase i) c * (-X j) ^ k * (((s i).descFactorial k : Poly) * X i ^ (s i - k)) := by
  conv_lhs => rw [monomial_eq_erase_mul (i := i)]
  exact lieOp_pow_apply hij _ (pderiv_monomial_erase s c) _ _

theorem lieOp_pow_monomial_eq_zero (hij : i ≠ j) (s : Fin 3 →₀ ℕ) (c : ℚ) (k : ℕ) (hk : s i < k) :
    (lieOp i j ^ k) (monomial s c) = 0 := by
  rw [lieOp_pow_monomial hij, (Nat.descFactorial_eq_zero_iff_lt).mpr hk]
  simp

/-- The shear on a monomial is the truncated exponential of `-x_j ∂_{x_i}`. -/
theorem shear_monomial_eq_sum (hij : i ≠ j) (s : Fin 3 →₀ ℕ) (c : ℚ) (N : ℕ) (hN : s i < N) :
    shear i j (monomial s c) = ∑ k ∈ range N, ((k.factorial : ℚ)⁻¹) • (lieOp i j ^ k) (monomial s c) := by
  set r := monomial (s.erase i) c with hr
  set m := s i with hm
  have hl : ∀ k, (lieOp i j ^ k) (monomial s c) = r * ((-X j) ^ k * ((m.descFactorial k : Poly) * X i ^ (m - k))) := fun k => by
    rw [lieOp_pow_monomial hij, mul_assoc]
  simp_rw [hl]
  conv_lhs => rw [monomial_eq_erase_mul (i := i)]
  rw [← hr, ← hm, map_mul, shear_monomial_erase hij, map_pow, shear_X]
  simp only [ite_true]
  have hsub : range (m + 1) ⊆ range N := range_subset_range.mpr hN
  rw [← Finset.sum_subset hsub]
  · rw [sub_eq_add_neg, add_comm, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Nat.descFactorial_eq_factorial_mul_choose, smul_eq_C_mul]
    simp only [Nat.cast_mul]
    have hk0 : ((k.factorial : ℚ)) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have : C ((k.factorial : ℚ)⁻¹) * (k.factorial : Poly) = 1 := by
      rw [← map_natCast C, ← C_mul, inv_mul_cancel₀ hk0, C_1]
    calc r * ((-X j) ^ k * X i ^ (m - k) * (m.choose k : Poly)) =
        r * (C ((k.factorial : ℚ)⁻¹) * (k.factorial : Poly)) * ((-X j) ^ k * X i ^ (m - k) * (m.choose k : Poly)) := by
          rw [this]; ring
      _ = _ := by ring
  · intro k _ hk
    have : m < k := by
      by_contra h
      exact hk (Finset.mem_range.mpr (by omega))
    rw [(Nat.descFactorial_eq_zero_iff_lt).mpr this]
    simp

end TernaryPeriodPolynomials.Argument.Identities
