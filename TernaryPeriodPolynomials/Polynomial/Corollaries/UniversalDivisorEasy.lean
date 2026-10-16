module

public import TernaryPeriodPolynomials.Polynomial.Restriction
public import TernaryPeriodPolynomials.Polynomial.PeriodNormalization
public import TernaryPeriodPolynomials.Polynomial.Divisibility
public import TernaryPeriodPolynomials.Polynomial.Defs

@[expose] public section


/-! The three "easy" linear factors of `universalDivisor` dividing any solution `f`, derived
directly from `PeriodRelations (restriction f)` and `f = cyclicLift (restriction f)` alone (no
symmetric/alternating sector split, hence available for both `universal_divisor_gcd` and
`torsion_free_descent`). -/


open MvPolynomial TernaryPoly TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument

variable {R : Type*} [CommRing R]

/-- `X0+X1` divides a solution, given the full period relations of its restriction. -/
theorem dvd_X0_add_X1 {f : Ternary R} (hCL : f = cyclicLift (restriction f))
    (hPR : PeriodRelations (restriction f)) : (X 0 + X 1 : Ternary R) ∣ f := by
  set q := restriction f with hqdef
  have hu0 : binaryEval q (X 0 : Ternary R) (X 0) = 0 := by
    have h3 := hPR.identities.eval_three_term (X 0 : Ternary R) (X 0)
    simp only [sub_self] at h3
    rwa [hPR.eval_zero_second, hPR.eval_zero_first, add_zero, add_zero] at h3
  have hu1 : binaryEval q (X 0 : Ternary R) (-X 0) = 0 := by
    have h2 := hPR.identities.eval_two_term (X 0 : Ternary R) (-X 0)
    rw [neg_neg] at h2
    rwa [hu0, add_zero] at h2
  have h2' := hPR.identities.eval_two_term (X 2 : Ternary R) (X 0)
  have hzero : bind₁ (Function.update X 1 (-X 0) : Fin 3 → Ternary R) f = 0 := by
    have hvec : (Function.update X 1 (-X 0) : Fin 3 → Ternary R) = ![X 0, -X 0, X 2] := by
      funext i; fin_cases i <;> simp
    rw [hvec, hCL, bind_cyclicLift]
    linear_combination hu1 + h2'
  have hdvd := linear_factor_dvd_of_substitution_zero f 1 (-X 0) hzero
  have he : (X 0 + X 1 : Ternary R) = X 1 - (-X 0) := by ring
  rwa [he]

/-- Applying the cyclic shift `S : (x,y,z) ↦ (y,z,x)` to a known divisibility of a solution `f`
(using `f`'s own cyclic invariance) yields the next cyclic rotate of the divisor. -/
private theorem dvd_cyclic_shift {f : Ternary R} (hf : Solution f) {d : Ternary R}
    (hd : d ∣ f) : bind₁ (![X 1, X 2, X 0] : Fin 3 → Ternary R) d ∣ f := by
  have h := map_dvd (bind₁ (![X 1, X 2, X 0] : Fin 3 → Ternary R)) hd
  rwa [hf.cyclic] at h

/-- `X1+X2` divides a solution, given the full period relations of its restriction. -/
theorem dvd_X1_add_X2 {f : Ternary R} (hf : Solution f)
    (hCL : f = cyclicLift (restriction f)) (hPR : PeriodRelations (restriction f)) :
    (X 1 + X 2 : Ternary R) ∣ f := by
  have h := dvd_cyclic_shift hf (dvd_X0_add_X1 hCL hPR)
  simpa using h

/-- `X2+X0` divides a solution, given the full period relations of its restriction. -/
theorem dvd_X2_add_X0 {f : Ternary R} (hf : Solution f)
    (hCL : f = cyclicLift (restriction f)) (hPR : PeriodRelations (restriction f)) :
    (X 2 + X 0 : Ternary R) ∣ f := by
  have h := dvd_cyclic_shift hf (dvd_X1_add_X2 hf hCL hPR)
  simpa using h

end TernaryPeriodPolynomials.Argument
