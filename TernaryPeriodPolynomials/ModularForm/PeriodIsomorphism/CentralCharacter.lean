module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.RepUnfolding

@[expose] public section


/-!
# Corollary 1.4, Step 1: the central character lemma

For `p : MvPolynomial (Fin 2) ℂ` homogeneous of even degree `n`, negating every variable fixes
`p`: `bind₁ (fun i => -X i) p = p`. This is the polynomial-level fact behind
`ρ(S) (ρ(S) x) = x` on the degree-`n` (even) summand of `modularBinaryRep`: `S^2` casts to `-1 : GL2`, whose substitution
action is exactly this negate-every-variable map.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open MvPolynomial
open GeneralEisenstein.Binary (Poly)

/-- Negating every variable fixes an even-degree homogeneous polynomial in two variables. -/
theorem bind₁_neg_X_of_isHomogeneous_even {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n)
    (hn : Even n) : bind₁ (fun i => -X i) p = p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [bind₁_monomial]
  have hdeg : (∑ i ∈ d.support, d i) = n := by
    rw [← Finsupp.degree_apply, Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp hd)
  have hprod : ∏ i ∈ d.support, (-X i) ^ d i = ∏ i ∈ d.support, (X i : Poly) ^ d i := by
    calc ∏ i ∈ d.support, (-X i) ^ d i
        = ∏ i ∈ d.support, ((-1 : Poly) ^ d i * (X i) ^ d i) := by
          apply Finset.prod_congr rfl; intro i _; rw [neg_pow]
      _ = (∏ i ∈ d.support, (-1 : Poly) ^ d i) * ∏ i ∈ d.support, (X i) ^ d i :=
          Finset.prod_mul_distrib
      _ = (-1 : Poly) ^ (∑ i ∈ d.support, d i) * ∏ i ∈ d.support, (X i) ^ d i := by
          rw [Finset.prod_pow_eq_pow_sum]
      _ = (-1 : Poly) ^ n * ∏ i ∈ d.support, (X i) ^ d i := by rw [hdeg]
      _ = ∏ i ∈ d.support, (X i) ^ d i := by rw [hn.neg_one_pow, one_mul]
  rw [hprod, monomial_eq]
  rfl

end TernaryPeriodPolynomials.Argument.Corollary14
