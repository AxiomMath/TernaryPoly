module

public import TernaryPeriodPolynomials.Polynomial.Divisibility
public import TernaryPeriodPolynomials.Polynomial.Definitions
public import TernaryPeriodPolynomials.Polynomial.Defs

@[expose] public section


/-! Regularity (non-zero-divisor) facts about small linear combinations of the three variables of
`Ternary R`, over any `CommRing R` (no `IsDomain` needed), and a generalized combinator that uses
them to multiply together several linear-factor divisibility facts about the same `f` without
needing `[IsDomain R]`. This is what lets `torsion_free_descent` assemble `universalDivisor R ∣ f`
from four single-factor facts over a merely torsion-free (possibly zero-divisor-having) `R`. -/


open MvPolynomial TernaryPoly TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument

variable {R : Type*} [CommRing R]

section Regularity

/-- Transport non-zero-divisor membership backwards along `MvPolynomial.finSuccEquiv`: this needs
only injectivity of the equivalence, which it has for free (no domain hypothesis anywhere). -/
theorem finSuccEquiv_mem_nonZeroDivisors {n : ℕ} {p : MvPolynomial (Fin (n + 1)) R}
    (h : MvPolynomial.finSuccEquiv R n p ∈
      nonZeroDivisors (Polynomial (MvPolynomial (Fin n) R))) :
    p ∈ nonZeroDivisors (MvPolynomial (Fin (n + 1)) R) := by
  set e := MvPolynomial.finSuccEquiv R n
  rw [mem_nonZeroDivisors_iff] at h ⊢
  refine ⟨fun z hz => e.injective ?_, fun z hz => e.injective ?_⟩
  · rw [map_zero]; exact h.1 (e z) (by rw [← map_mul, hz, map_zero])
  · rw [map_zero]; exact h.2 (e z) (by rw [← map_mul, hz, map_zero])

/-- `X0+X1` is a non-zero-divisor in `Ternary R`, for any `CommRing R`. -/
theorem X0_add_X1_mem_nonZeroDivisors : (X 0 + X 1 : Ternary R) ∈ nonZeroDivisors (Ternary R) := by
  apply finSuccEquiv_mem_nonZeroDivisors
  have h01 : (1 : Fin 3) = (0 : Fin 2).succ := rfl
  rw [map_add, finSuccEquiv_X_zero, h01, finSuccEquiv_X_succ]
  exact (Polynomial.monic_X_add_C _).mem_nonZeroDivisors

/-- `X0+X2` is a non-zero-divisor in `Ternary R`, for any `CommRing R`. -/
theorem X0_add_X2_mem_nonZeroDivisors : (X 0 + X 2 : Ternary R) ∈ nonZeroDivisors (Ternary R) := by
  apply finSuccEquiv_mem_nonZeroDivisors
  have h21 : (2 : Fin 3) = (1 : Fin 2).succ := rfl
  rw [map_add, finSuccEquiv_X_zero, h21, finSuccEquiv_X_succ]
  exact (Polynomial.monic_X_add_C _).mem_nonZeroDivisors

/-- `X0-X1` is a non-zero-divisor in `Ternary R`, for any `CommRing R`. -/
theorem X0_sub_X1_mem_nonZeroDivisors : (X 0 - X 1 : Ternary R) ∈ nonZeroDivisors (Ternary R) := by
  apply finSuccEquiv_mem_nonZeroDivisors
  have h01 : (1 : Fin 3) = (0 : Fin 2).succ := rfl
  rw [map_sub, finSuccEquiv_X_zero, h01, finSuccEquiv_X_succ, sub_eq_add_neg, ← map_neg]
  exact (Polynomial.monic_X_add_C _).mem_nonZeroDivisors

/-- Negation preserves non-zero-divisor status. -/
theorem neg_mem_nonZeroDivisors {a : Ternary R} (ha : a ∈ nonZeroDivisors (Ternary R)) :
    -a ∈ nonZeroDivisors (Ternary R) := by
  have hneg1 : (-1 : Ternary R) ∈ nonZeroDivisors (Ternary R) :=
    (isUnit_one.neg).mem_nonZeroDivisors
  simpa using mul_mem hneg1 ha

end Regularity

section EasyDirection

/-- The easy direction of `TernaryPoly.linear_factor_dvd_of_substitution_zero`: if `X i - p`
(with `p` fixed by the substitution `update i p`, i.e. not involving `X i`) divides `f`, then `f`
vanishes under `update i p`. Needs no domain hypothesis: substituting `X i ↦ p` kills the factor
`X i - p` itself, so the whole product vanishes. -/
theorem substitution_zero_of_dvd {σ : Type*} [DecidableEq σ]
    (f : MvPolynomial σ R) (i : σ) (p : MvPolynomial σ R)
    (hp : bind₁ (Function.update X i p) p = p) (hd : (X i - p) ∣ f) :
    bind₁ (Function.update X i p) f = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rw [map_mul]
  have hz : bind₁ (Function.update X i p) (X i - p) = 0 := by
    rw [map_sub, bind₁_X_right, Function.update_self, hp, sub_self]
  rw [hz, zero_mul]

/-- Like `TernaryPoly.mul_linear_factor_dvd_of_substitution_zero`, but replacing the
`[IsDomain R]`-dependent hypothesis `bind₁ (update i p) d ≠ 0` by the strictly weaker (and
domain-free) hypothesis that this image is a non-zero-divisor — exactly the condition under which
the needed cancellation `a * b = 0 → b = 0` holds in *any* commutative ring. -/
theorem mul_linear_factor_dvd_of_substitution_zero' {σ : Type*} [DecidableEq σ]
    (f d : MvPolynomial σ R) (i : σ) (p : MvPolynomial σ R)
    (hd : d ∣ f) (hf : bind₁ (Function.update X i p) f = 0)
    (hkeep : bind₁ (Function.update X i p) d ∈ nonZeroDivisors (MvPolynomial σ R)) :
    (d * (X i - p)) ∣ f := by
  obtain ⟨q, rfl⟩ := hd
  have hq : bind₁ (Function.update X i p) q = 0 := by
    rw [map_mul] at hf
    exact (mem_nonZeroDivisors_iff.mp hkeep).1 _ hf
  obtain ⟨r, hr⟩ := linear_factor_dvd_of_substitution_zero q i p hq
  exact ⟨r, by rw [hr, mul_assoc]⟩

end EasyDirection

end TernaryPeriodPolynomials.Argument
