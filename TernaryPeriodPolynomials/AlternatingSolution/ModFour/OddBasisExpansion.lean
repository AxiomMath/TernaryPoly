module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.CoefficientParity

@[expose] public section



/-! Odd mirror of `TernaryPoly.CharTwoNorm.even_basis_expansion`. Used in the proof of
Theorem 5.2 (`mf:thm:main`), step `mf:lem:cancellation` (GAP A): once `degreeEuler g = g` is
known (via `hasOddMonomials_degreeEuler_eq_self` applied after cancelling the even factor
`a*cplus`), this extracts a basis expansion of `g` entirely in the "odd" shape, i.e. with the
factor `d7` attached to the *even*-indexed (`basisOdd i = false`) basis elements rather than
the odd-indexed ones. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument

/-- Odd mirror of `even_basis_expansion`: if `degreeEuler g = g` (rather than `= 0`), the
basis expansion can be rearranged so that `d7` is attached exactly to the even-indexed basis
elements. -/
theorem odd_basis_expansion {g : Poly} (ho : degreeEuler g = g)
    (q : Fin 8 → Poly) (hq : g = ∑ i, invariantEval (q i)*basis i) :
    ∃ r : Fin 8 → Poly, g = ∑ i,
      (if basisOdd i then invariantEvenEval (r i) else d7*invariantEvenEval (r i))*basis i := by
  classical
  choose p r hr using fun i => invariant_parity_split (q i)
  let ev : Fin 8 → Poly := fun i =>
    (if basisOdd i then d7*invariantEvenEval (r i) else invariantEvenEval (p i))*basis i
  let od : Fin 8 → Poly := fun i =>
    (if basisOdd i then invariantEvenEval (p i) else d7*invariantEvenEval (r i))*basis i
  have hsplit : g = (∑ i, ev i)+(∑ i, od i) := by
    rw [hq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hr]
    cases hb : basisOdd i <;> simp [ev, od, hb] <;> ring
  have hev (i : Fin 8) : degreeEuler (ev i) = 0 := by
    cases hb : basisOdd i <;>
      simp [ev, hb, degreeEuler_mul, degreeEuler_invariantEvenEval, degreeEuler_d7,
        degreeEuler_basis, CharTwo.add_self_eq_zero]
  have hod (i : Fin 8) : degreeEuler (od i) = od i := by
    cases hb : basisOdd i <;>
      simp [od, hb, degreeEuler_mul, degreeEuler_invariantEvenEval, degreeEuler_d7,
        degreeEuler_basis]
  have hstar : degreeEuler g = ∑ i, od i := by
    have h := congrArg degreeEuler hsplit
    simpa only [degreeEuler_add, degreeEuler_sum, hev, hod, Finset.sum_const_zero,
      zero_add] using h
  refine ⟨fun i => if basisOdd i then p i else r i, ?_⟩
  rw [← ho, hstar]
  apply Finset.sum_congr rfl
  intro i _
  cases hb : basisOdd i <;> simp [od, hb]

end TernaryPeriodPolynomials.Argument
