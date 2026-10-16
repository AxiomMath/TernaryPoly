module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.CoefficientParity
public import TernaryPeriodPolynomials.Polynomial.CharTwo.MultiplierFactor
public import TernaryPeriodPolynomials.AlternatingSolution.CoefficientPolynomials
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.DegreeEulerOdd
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.OddBasisExpansion

@[expose] public section



/-! (`mf:lem:cancellation`) of the proof of Theorem 5.2 (`mf:thm:main`): every symmetric
`h : Poly2` with `HasOddMonomials h` and `TernaryPoly.CharTwoNorm.norm h = 0` has an `expandOdd`
expansion `h = expandOdd r` for some `r : Fin 8 → Poly2`.

Strategy: `charTwo_normKernel_free` gives `h = ∑ j, invariantEval (q j) * generator j` for some `q`. Since
`generator j = a * cplus * basis j`, this factors as `h = a * cplus * g` with
`g = ∑ i, invariantEval (q i) * basis i`. The hypothesis `HasOddMonomials h` makes `h` fixed by
the Euler derivation `degreeEuler` (`DegreeEulerOdd.lean`); since `a * cplus` is homogeneous of
*even* degree `4`, `degreeEuler (a * cplus) = 0`, so the Leibniz rule `degreeEuler_mul` and
cancelling the nonzero factor `a * cplus` shows `g` is itself fixed by `degreeEuler`. Then
`odd_basis_expansion` rewrites `g`'s basis expansion into the shape with `d7` attached to the
*even*-indexed basis elements, which (since `evalR0 = invariantEvenEval` and `kappa`/`basisOdd`
are complementary) is exactly `a * cplus` times the basis expansion of `expandOdd` termwise. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument

/-- `evalR0` and `invariantEvenEval` are the same evaluation map, both `bind₁ ![d4, d6, d7^2]`
(the former named for the `(p,q,ρ)`-formal-polynomial role, the latter for the `(x,y,z)` role —
`Poly` and `Poly2` are the same reducible type). -/
theorem evalR0_eq_invariantEvenEval : evalR0 = invariantEvenEval := rfl

/-- The per-generator identity turning a term of `expandOdd` into an `a * cplus`-multiple of a
basis term, matching the "odd" shape of `odd_basis_expansion`'s conclusion. -/
theorem evalR0_mul_oddGenerator_eq_ac (p : Poly2) (j : Fin 8) :
    evalR0 p * oddGenerator j
      = a * cplus * ((if basisOdd j then invariantEvenEval p else d7 * invariantEvenEval p)
          * basis j) := by
  show evalR0 p * (generator j * d7 ^ kappa j) = _
  rw [evalR0_eq_invariantEvenEval]
  show invariantEvenEval p * (a * cplus * basis j * d7 ^ kappa j) = _
  fin_cases j <;> simp [kappa, basisOdd] <;> ring

/-- GAP A: a symmetric `h` with `HasOddMonomials h` and zero norm expands as `expandOdd r`. -/
theorem expandOdd_exists_of_odd_symmetric {h : Poly2} (hsymm : h.IsSymmetric)
    (hodd : HasOddMonomials h) (hn : TernaryPoly.CharTwoNorm.norm h = 0) :
    ∃ r : Fin 8 → Poly2, h = expandOdd r := by
  obtain ⟨q, hq, -⟩ := (charTwo_normKernel_free.2 h hsymm).mp hn
  let g : Poly2 := ∑ i, invariantEval (q i) * basis i
  have hg_def : g = ∑ i, invariantEval (q i) * basis i := rfl
  have hgen : h = a * cplus * g := by
    rw [hq, hg_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    show invariantEval (q i) * (a * cplus * basis i) = a * cplus * (invariantEval (q i) * basis i)
    ring
  have hac_even : degreeEuler (a * cplus) = 0 :=
    degreeEuler_eq_zero_of_even (a_homogeneous.mul cplus_homogeneous) (by decide)
  have hac_ne : a * cplus ≠ 0 := mul_ne_zero a_ne_zero cplus_ne_zero
  have hh_fixed : degreeEuler h = h := hasOddMonomials_degreeEuler_eq_self hodd
  have hg_fixed : degreeEuler g = g := by
    apply mul_left_cancel₀ hac_ne
    have hstep : degreeEuler (a * cplus * g) = a * cplus * degreeEuler g := by
      rw [degreeEuler_mul, hac_even, zero_mul, zero_add]
    calc a * cplus * degreeEuler g = degreeEuler (a * cplus * g) := hstep.symm
      _ = degreeEuler h := by rw [hgen]
      _ = h := hh_fixed
      _ = a * cplus * g := hgen
  obtain ⟨r', hr'⟩ := odd_basis_expansion hg_fixed q hg_def
  refine ⟨r', ?_⟩
  show h = ∑ i, evalR0 (r' i) * oddGenerator i
  rw [hgen, hr', Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => (evalR0_mul_oddGenerator_eq_ac (r' i) i).symm)

end TernaryPeriodPolynomials.Argument
