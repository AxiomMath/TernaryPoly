module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Basic

@[expose] public section


open Polynomial

namespace TernaryPoly

/-- Hasse derivatives commute with coefficient maps in arbitrary characteristic. -/
theorem map_hasseDeriv {R S : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (k : ℕ) (p : Polynomial R) :
    Polynomial.map φ (hasseDeriv k p) = hasseDeriv k (Polynomial.map φ p) := by
  ext n
  simp only [coeff_map, hasseDeriv_coeff, map_mul, map_natCast]

/-- Todd operators commute with maps of their rational coefficient algebras. -/
theorem map_todd {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (φ : R →ₐ[ℚ] S) (u : R) (p : Polynomial R) :
    Polynomial.map φ.toRingHom (todd u p) =
      todd (φ u) (Polynomial.map φ.toRingHom p) := by
  have hdegree : (Polynomial.map φ.toRingHom p).natDegree < p.natDegree+1 :=
    lt_of_le_of_lt natDegree_map_le (Nat.lt_succ_self _)
  rw [todd_eq_sum u p (p.natDegree+1) (Nat.lt_succ_self _),
    todd_eq_sum (φ u) (Polynomial.map φ.toRingHom p) (p.natDegree+1) hdegree,
    Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.map_smul, map_hasseDeriv]
  have hcoeff : φ.toRingHom (algebraMap ℚ R (bernoulli k) * (-u)^k) =
      algebraMap ℚ S (bernoulli k) * (-φ u)^k := by
    change φ (algebraMap ℚ R (bernoulli k) * (-u)^k) = _
    rw [map_mul, map_pow, map_neg, φ.commutes]
  rw [hcoeff]

end TernaryPoly
