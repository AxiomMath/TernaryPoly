module

public import TernaryPeriodPolynomials.Polynomial.Defs

@[expose] public section


/-! Norm-value computation for the sharpness example for Theorem 5.2 (`mf:thm:main`). -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- `N f = 6xy(x-y)(x²-xy+y²-z²)` for `f = (x+y+z)²(x-y)(x-z)(y-z)`. -/
theorem sharp_norm_eq :
    threeTermNorm ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
      MvPolynomial (Fin 3) ℤ) =
      C 6 * X 0 * X 1 * (X 0 - X 1) * (X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2 - X 2 ^ 2) := by
  simp [threeTermNorm, bind₁_X_right]
  ring

end TernaryPeriodPolynomials.Argument
