module

public import TernaryPeriodPolynomials.Polynomial.Classification.Restriction
public import TernaryPeriodPolynomials.Polynomial.Support
public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section


/-!
# Theorem 1.1: solutions of the cyclic three-term relations

Let `F` be a field of characteristic zero. If `f ∈ F[x, y, z]` satisfies `f(x, y, z) = f(y, z, x)`
and `f(x, y, z) + f(-y, x - y, z) + f(y - x, -x, z) = 0`, then `f = P(x, y) + Q(y, z) + R(z, x)`,
equivalently `∂ₓ∂ᵧ∂_z f = 0`, and `f = 0` if `f` is homogeneous of odd degree
(`TernaryPeriodPolynomials.bachmann_van_ittersum`). This proves the conjecture of Bachmann and
van Ittersum.

The proof combines the pairwise decomposition `Argument.Classification.solution_pairwise`, obtained
through the boundary comparison of the paper (Sections 3–6), with the vanishing of odd-degree
solutions `Argument.Classification.solution_odd_eq_zero`.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.Classification

/-- Over a `ℚ`-algebra the mixed third partial derivative `∂ₓ∂ᵧ∂_z f` of every solution `f`
vanishes: a solution is a sum of polynomials in two of the variables. -/
theorem solution_mixed_derivative_eq_zero {R : Type*} [CommRing R] [Algebra ℚ R]
    (f : TernaryPoly.Paper.Ternary R) (hf : TernaryPoly.Paper.Solution f) :
    pderiv 0 (pderiv 1 (pderiv 2 f)) = 0 :=
  (TernaryPoly.Paper.pairwise_iff_mixed_derivative_eq_zero f).mp (solution_pairwise f hf)

end TernaryPeriodPolynomials.Argument.Classification

namespace TernaryPeriodPolynomials

/-- **Theorem 1.1** (conjecture of Bachmann–van Ittersum). Let `F` be a field of characteristic
zero and let `f ∈ F[x, y, z]` satisfy `f(x, y, z) = f(y, z, x)` and
`f(x, y, z) + f(-y, x - y, z) + f(y - x, -x, z) = 0`. Then `f = P(x, y) + Q(y, z) + R(z, x)` for
binary polynomials `P, Q, R`, the mixed derivative `∂ₓ∂ᵧ∂_z f` vanishes, and every homogeneous
such `f` of odd degree is zero. -/
theorem bachmann_van_ittersum {F : Type*} [Field F] [CharZero F] (f : MvPolynomial (Fin 3) F)
    (hcyclic : bind₁ ![X 1, X 2, X 0] f = f)
    (hnorm : f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) :
    (∃ p q r : MvPolynomial (Fin 2) F,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q +
        rename (![2, 0] : Fin 2 → Fin 3) r) ∧
    pderiv 0 (pderiv 1 (pderiv 2 f)) = 0 ∧
    (∀ n, f.IsHomogeneous n → Odd n → f = 0) := by
  have hsol : TernaryPoly.Paper.Solution f := ⟨hcyclic, hnorm⟩
  refine ⟨(Argument.Classification.solution_pairwise f hsol).exists_cyclic_rename,
    Argument.Classification.solution_mixed_derivative_eq_zero f hsol, ?_⟩
  intro n hn hodd
  exact Argument.Classification.solution_odd_eq_zero hn hsol hodd

end TernaryPeriodPolynomials
