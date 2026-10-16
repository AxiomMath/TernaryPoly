module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.ReduceTwoBasic
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.ThreeTermNormNaturality
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.OddKernelCancellation
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.ExpandOddKernel
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.OperatorAdditivity
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.ReduceTwoHalving
public import TernaryPeriodPolynomials.AlternatingSolution.TriangularTable

@[expose] public section



/-! Combined proof of `even_coefficients_of_four_dvd_norm` (`mf:thm:main`): assembles the full mod-four argument into the final statement.

Given `f` alternating with `HasOddMonomials f` and `threeTermNorm f = C 4 * g0`: write
`C 4 * g0 = C 2 * (C 2 * g0)`, so `h := reduceTwo f` is symmetric
(`alternating_reduceTwo_symmetric`), has `HasOddMonomials` (`reduceTwo_hasOddMonomials`), and has
zero `TernaryPoly.CharTwoNorm.norm` (`reduceTwo_threeTermNorm` + `reduceTwo_two_mul`). GAP A
(`OddKernelCancellation.lean`) gives `r` with `h = expandOdd r`. Feeding `r`, `f`, `C 2 * g0` into
`modFour_beta_triangular`'s alternating clause and simplifying `reduceTwo (C 2 * g0) = 0` /
`piOperator 0 = 0` gives `expandOdd r + expandOdd (uOperator r) = 0`. GAP B
(`ExpandOddKernel.lean`) turns this into `r = 0`, so `h = expandOdd 0 = 0`, i.e.
`reduceTwo f = 0`; `exists_half_of_reduceTwo_eq_zero` (`ReduceTwoHalving.lean`) concludes. -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- Combined proof of `even_coefficients_of_four_dvd_norm`. -/
theorem theorem_5_2_proof (f : MvPolynomial (Fin 3) ℤ) (halt : IsAlternating f)
    (hodd : HasOddMonomials f) (hN : ∃ g : MvPolynomial (Fin 3) ℤ, threeTermNorm f = C 4 * g) :
    ∃ g : MvPolynomial (Fin 3) ℤ, f = C 2 * g := by
  obtain ⟨g0, hg0⟩ := hN
  have hg0' : threeTermNorm f = C 2 * (C 2 * g0) := by
    rw [hg0, show (4 : ℤ) = 2 * 2 from by norm_num, map_mul, mul_assoc]
  have hn0 : TernaryPoly.CharTwoNorm.norm (reduceTwo f) = 0 := by
    have h1 : reduceTwo (threeTermNorm f) = TernaryPoly.CharTwoNorm.norm (reduceTwo f) :=
      reduceTwo_threeTermNorm f
    rw [hg0', reduceTwo_two_mul] at h1
    exact h1.symm
  obtain ⟨r, hr⟩ := expandOdd_exists_of_odd_symmetric
    (alternating_reduceTwo_symmetric halt) (reduceTwo_hasOddMonomials hodd) hn0
  have hstep3 : piOperator (reduceTwo (C 2 * g0)) = expandOdd r + expandOdd (uOperator r) :=
    (modFour_beta_triangular.1 r f (C 2 * g0) hr hg0').2 halt
  rw [reduceTwo_two_mul, piOperator_zero] at hstep3
  have hr0 : r = 0 := r_eq_zero_of_expandOdd_sum_eq_zero r hstep3.symm
  have hreduce0 : reduceTwo f = 0 := by rw [hr, hr0, expandOdd_zero]
  exact exists_half_of_reduceTwo_eq_zero hreduce0

end TernaryPeriodPolynomials.Argument
