module

public import TernaryPeriodPolynomials.Polynomial.RestrictionEquiv
public import TernaryPeriodPolynomials.Polynomial.Divisibility

@[expose] public section


/-! The fourth linear factor `X0+X1+X2` of `universalDivisor`, dividing a solution lying in a
single symmetric or alternating sector (under the swap `S : (x,y,z) ↦ (y,z,x)`). Unlike the three
"easy" factors (`UniversalDivisorEasy.lean`), this one genuinely needs the sector hypothesis. -/


open MvPolynomial TernaryPoly TernaryPoly.Paper
open TernaryPeriodPolynomials.Argument.Classification
open TernaryPeriodPolynomials.Argument.RouteIndependent

namespace TernaryPeriodPolynomials.Argument

variable {R : Type*} [CommRing R]

/-- Shared wiring: given the key numeric identity at the triple `(X0,X1,-X0-X1)`, assemble the
fourth factor's divisibility. Sector-independent. -/
private theorem dvd_X0_add_X1_add_X2_of_eval_sum {g : Ternary R}
    (hCL : g = cyclicLift (restriction g))
    (hsum : binaryEval (restriction g) (X 0 : Ternary R) (X 1) +
        binaryEval (restriction g) (X 1 : Ternary R) (-(X 0 + X 1)) +
        binaryEval (restriction g) (-(X 0 + X 1) : Ternary R) (X 0) = 0) :
    (X 0 + X 1 + X 2 : Ternary R) ∣ g := by
  have hvec : (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary R) = ![X 0, X 1, -X 0 - X 1] := by
    funext i; fin_cases i <;> simp
  have hzero : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary R) g = 0 := by
    rw [hvec, hCL, bind_cyclicLift]
    have hcX : (-X 0 - X 1 : Ternary R) = -(X 0 + X 1) := by ring
    rw [hcX]
    exact hsum
  have hdvd := linear_factor_dvd_of_substitution_zero g 2 (-X 0 - X 1) hzero
  have heq : (X 0 + X 1 + X 2 : Ternary R) = X 2 - (-X 0 - X 1) := by ring
  rwa [heq]

/-- The fourth factor, for a solution in the **symmetric** sector (`S g = g`). -/
theorem dvd_X0_add_X1_add_X2_of_symmetric [Algebra ℚ R] {g : Ternary R} (hg : Solution g)
    (hCL : g = cyclicLift (restriction g)) (hPR : PeriodRelations (restriction g))
    (hSym : bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) g = g) :
    (X 0 + X 1 + X 2 : Ternary R) ∣ g := by
  apply dvd_X0_add_X1_add_X2_of_eval_sum hCL
  set q := restriction g with hqdef
  have ho : bind₁ (![-X 0, X 1] : Fin 2 → Binary R) q = -q :=
    (TernaryPeriodPolynomials.Argument.Classification.restriction_symmetric_iff hg).mp hSym
  clear_value q
  have hT1' : binaryEval q (-X 1 : Ternary R) (X 0) = -binaryEval q (X 0) (X 1) := by
    have b1 := binaryEval_odd_first ho (X 1 : Ternary R) (X 0)
    have b2 := hPR.eval_swap_of_odd ho (X 0 : Ternary R) (X 1)
    linear_combination b1 - b2
  have hT3' : binaryEval q (-(X 0 + X 1) : Ternary R) (X 0) = -binaryEval q (X 0) (X 0 + X 1) := by
    have a3 := binaryEval_odd_first ho (X 0 + X 1 : Ternary R) (X 0)
    have a4 := hPR.eval_swap_of_odd ho (X 0 : Ternary R) (X 0 + X 1)
    linear_combination a3 - a4
  have hnR : binaryEval q (-X 0 : Ternary R) (-(X 0 + X 1)) = binaryEval q (X 0) (X 0 + X 1) := by
    have a1 := binaryEval_odd_first ho (X 0 : Ternary R) (-(X 0 + X 1))
    have a2 := hPR.eval_swap_of_odd ho (X 0 : Ternary R) (-(X 0 + X 1))
    have a3 := binaryEval_odd_first ho (X 0 + X 1 : Ternary R) (X 0)
    have a4 := hPR.eval_swap_of_odd ho (X 0 : Ternary R) (X 0 + X 1)
    linear_combination a1 + a2 - a3 + a4
  have hT2' : binaryEval q (X 1 : Ternary R) (-(X 0 + X 1)) = -binaryEval q (X 0 + X 1) (X 1) := by
    have d1 := hPR.eval_swap_of_odd ho (-(X 0 + X 1) : Ternary R) (X 1)
    have d2 := binaryEval_odd_first ho (X 0 + X 1 : Ternary R) (X 1)
    linear_combination d1 + d2
  have h3 := hPR.identities.eval_three_term (X 0 + X 1 : Ternary R) (X 1)
  have harg1 : (X 0 + X 1 - X 1 : Ternary R) = X 0 := by ring
  have harg2 : (X 1 - (X 0 + X 1) : Ternary R) = -X 0 := by ring
  rw [harg1, harg2, hT1', hnR] at h3
  rw [hT2', hT3']
  linear_combination -h3

/-- The fourth factor, for a solution in the **alternating** sector (`S g = -g`). -/
theorem dvd_X0_add_X1_add_X2_of_alternating [Algebra ℚ R] {g : Ternary R} (hg : Solution g)
    (hCL : g = cyclicLift (restriction g)) (hPR : PeriodRelations (restriction g))
    (hAlt : bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) g = -g) :
    (X 0 + X 1 + X 2 : Ternary R) ∣ g := by
  apply dvd_X0_add_X1_add_X2_of_eval_sum hCL
  set q := restriction g with hqdef
  have he : bind₁ (![-X 0, X 1] : Fin 2 → Binary R) q = q :=
    (TernaryPeriodPolynomials.Argument.RouteIndependent.restriction_alternating_iff hg).mp hAlt
  clear_value q
  have hT1' : binaryEval q (-X 1 : Ternary R) (X 0) = -binaryEval q (X 0) (X 1) := by
    have b1 := binaryEval_even_first he (X 1 : Ternary R) (X 0)
    have b2 := hPR.eval_swap_of_even he (X 0 : Ternary R) (X 1)
    linear_combination b1 + b2
  have hT3' : binaryEval q (-(X 0 + X 1) : Ternary R) (X 0) = -binaryEval q (X 0) (X 0 + X 1) := by
    have c1 := binaryEval_even_first he (X 0 + X 1 : Ternary R) (X 0)
    have c2 := hPR.eval_swap_of_even he (X 0 : Ternary R) (X 0 + X 1)
    linear_combination c1 + c2
  have hnR : binaryEval q (-X 0 : Ternary R) (-(X 0 + X 1)) = binaryEval q (X 0) (X 0 + X 1) := by
    have a1 := binaryEval_even_first he (X 0 : Ternary R) (-(X 0 + X 1))
    have a2 := hPR.eval_swap_of_even he (X 0 : Ternary R) (-(X 0 + X 1))
    have a3 := binaryEval_even_first he (X 0 + X 1 : Ternary R) (X 0)
    have a4 := hPR.eval_swap_of_even he (X 0 : Ternary R) (X 0 + X 1)
    linear_combination a1 + a2 - a3 - a4
  have hT2' : binaryEval q (X 1 : Ternary R) (-(X 0 + X 1)) = -binaryEval q (X 0 + X 1) (X 1) := by
    have d1 := hPR.eval_swap_of_even he (-(X 0 + X 1) : Ternary R) (X 1)
    have d2 := binaryEval_even_first he (X 0 + X 1 : Ternary R) (X 1)
    linear_combination d1 - d2
  have h3 := hPR.identities.eval_three_term (X 0 + X 1 : Ternary R) (X 1)
  have harg1 : (X 0 + X 1 - X 1 : Ternary R) = X 0 := by ring
  have harg2 : (X 1 - (X 0 + X 1) : Ternary R) = -X 0 := by ring
  rw [harg1, harg2, hT1', hnR] at h3
  rw [hT2', hT3']
  linear_combination -h3

end TernaryPeriodPolynomials.Argument
