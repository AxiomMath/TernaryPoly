module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Theorem52SharpProof

@[expose] public section


/-! Target: the sharpness example after Theorem 5.2 (`mf:thm:main`). -/

open MvPolynomial

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Sharpness of Theorem 5.2.** For `f = (x+y+z)²(x-y)(x-z)(y-z)`, which is alternating with
odd monomials, `N f = 6xy(x-y)(x²-xy+y²-z²)`; thus `N f ∈ 2ℤ[x,y,z]` although `f` does not
have even coefficients. -/
theorem four_dvd_norm_sharp :
    IsAlternating ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
      MvPolynomial (Fin 3) ℤ) ∧
    HasOddMonomials ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
      MvPolynomial (Fin 3) ℤ) ∧
    threeTermNorm ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
      MvPolynomial (Fin 3) ℤ) =
      C 6 * X 0 * X 1 * (X 0 - X 1) * (X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2 - X 2 ^ 2) ∧
    ¬ ∃ g : MvPolynomial (Fin 3) ℤ,
      ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
        MvPolynomial (Fin 3) ℤ) = C 2 * g := by
  exact theorem_5_2_sharp_proof

end TernaryPeriodPolynomials
