module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases

@[expose] public section



/-!
`IsSymmetric` closure facts for the quadrant multipliers `mult m`, the base witnesses
`baseSym j m`, and `evalSquaredLift P` for any integral `P`. These are the symmetric-ness
facts needed to show the global witness `v* := ∑ evalSquaredLift (P_m) * baseSym j m`
assembled for `modFour_beta_triangular`'s symmetric conjunct is itself symmetric.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-- Each quadrant multiplier `mult m` is symmetric. -/
theorem mult_isSymmetric (m : Fin 4) : (mult m : MvPolynomial (Fin 3) ℤ).IsSymmetric := by
  fin_cases m
  · simp [mult]
  · simpa [mult] using liftD6_isSymmetric
  · simpa [mult] using liftD4_isSymmetric
  · simpa [mult] using liftD4_isSymmetric.mul liftD6_isSymmetric

/-- `baseSym j m` is symmetric for every `j`, `m`. -/
theorem baseSym_isSymmetric (j : Fin 8) (m : Fin 4) :
    (baseSym j m : MvPolynomial (Fin 3) ℤ).IsSymmetric :=
  (mult_isSymmetric m).mul (oddGenLiftSym_isSymmetric j)

/-- `evalSquaredLift P` is symmetric for any integral `P`. -/
theorem evalSquaredLift_isSymmetric (P : MvPolynomial (Fin 3) ℤ) :
    (evalSquaredLift P).IsSymmetric := by
  unfold evalSquaredLift
  apply bind₁_isSymmetric_of_symmetric
  intro i
  fin_cases i
  · exact isSymmetric_pow liftD4_isSymmetric 2
  · exact isSymmetric_pow liftD6_isSymmetric 2
  · exact isSymmetric_pow liftD7_isSymmetric 2

end TernaryPeriodPolynomials.Argument.ModFourBeta
