module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Basic

@[expose] public section


/-!
# Injectivity of the canonical Todd operator

The zeroth Hasse term is the identity, and every positive Hasse term has zero
coefficient at the input's highest degree. This works over every commutative
rational algebra, including rings with zero divisors.
-/

open Polynomial

noncomputable section

namespace TernaryPoly

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The Todd operator preserves the coefficient at the input's highest degree. -/
theorem todd_coeff_natDegree (u : R) (p : Polynomial R) :
    (todd u p).coeff p.natDegree = p.coeff p.natDegree := by
  classical
  rw [todd_apply, finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp [_root_.bernoulli_zero]
  · intro k _ hk
    rw [coeff_smul, hasseDeriv_coeff,
      coeff_eq_zero_of_natDegree_lt (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hk)),
      mul_zero, smul_zero]
  · simp

/-- No nonzero polynomial is killed by the canonical Todd operator. -/
@[simp] theorem todd_eq_zero_iff (u : R) (p : Polynomial R) :
    todd u p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    apply leadingCoeff_eq_zero.mp
    rw [← coeff_natDegree, ← todd_coeff_natDegree u p, hp, coeff_zero]
  · intro hp
    rw [hp, map_zero]

/-- The canonical Todd operator is injective without a domain hypothesis. -/
theorem todd_injective (u : R) : Function.Injective (todd u) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply (todd_eq_zero_iff u (p - q)).mp
  rw [map_sub, hpq, sub_self]

/-- Todd preserves the natural degree, also at zero. -/
@[simp] theorem natDegree_todd (u : R) (p : Polynomial R) :
    (todd u p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  · apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_todd_le u p)
    rw [todd_coeff_natDegree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp

/-- Todd preserves the leading coefficient. -/
@[simp] theorem leadingCoeff_todd (u : R) (p : Polynomial R) :
    (todd u p).leadingCoeff = p.leadingCoeff := by
  rw [← coeff_natDegree, natDegree_todd, todd_coeff_natDegree, coeff_natDegree]

/-- Todd preserves the degree with its separate bottom value at zero. -/
@[simp] theorem degree_todd (u : R) (p : Polynomial R) :
    (todd u p).degree = p.degree := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [degree_eq_natDegree ((todd_eq_zero_iff u p).not.mpr hp),
      degree_eq_natDegree hp, natDegree_todd]

end TernaryPoly
