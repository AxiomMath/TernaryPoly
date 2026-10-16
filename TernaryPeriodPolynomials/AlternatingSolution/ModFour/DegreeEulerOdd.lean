module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.CoefficientParity

@[expose] public section



/-! Odd-degree mirror of `TernaryPoly.CharTwoNorm.degreeEuler_eq_zero_of_even`, and its
corollary for `HasOddMonomials`. Used in the proof of Theorem 5.2 (`mf:thm:main`), step
`mf:lem:cancellation` (GAP A): the mod-two reduction `h` of an alternating `f` with
`HasOddMonomials f` is fixed by the Euler degree-derivation `degreeEuler`, which lets the
common factor `a*cplus` be cancelled from a `charTwo_normKernel_free`-style generator expansion of `h`. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument

/-- Homogeneous polynomials of odd degree are fixed by the degree derivation `degreeEuler`.
Mirror of `TernaryPoly.CharTwoNorm.degreeEuler_eq_zero_of_even`. -/
theorem degreeEuler_eq_self_of_odd {g : Poly} {n : ℕ}
    (hg : g.IsHomogeneous n) (ho : Odd n) : degreeEuler g = g := by
  have h : (∑ i : Fin 3, X i * pderiv i g) = (n : ZMod 2) • g := by
    simpa only [Nat.cast_smul_eq_nsmul] using hg.sum_X_mul_pderiv
  rw [ho.natCast_zmod_two, one_smul] at h
  simpa only [Fin.sum_univ_three, degreeEuler] using h

/-- Any `h` all of whose monomials have odd total degree is fixed by `degreeEuler`. -/
theorem hasOddMonomials_degreeEuler_eq_self {h : Poly} (hh : HasOddMonomials h) :
    degreeEuler h = h := by
  have hdecomp : h = ∑ d ∈ h.support, monomial d (h.coeff d) :=
    (support_sum_monomial_coeff h).symm
  rw [hdecomp, degreeEuler_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hodd : Odd (d 0 + d 1 + d 2) := hh d hd
  have hg : (monomial d (h.coeff d)).IsHomogeneous (d 0 + d 1 + d 2) :=
    isHomogeneous_monomial _ (by rw [Finsupp.degree_eq_sum, Fin.sum_univ_three])
  exact degreeEuler_eq_self_of_odd hg hodd

end TernaryPeriodPolynomials.Argument
