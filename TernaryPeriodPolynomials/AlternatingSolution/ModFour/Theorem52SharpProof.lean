module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.SharpAlternating
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.SharpOddMonomials
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.SharpNormEq
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.SharpNotEven

@[expose] public section


/-! Combined proof of the sharpness example after Theorem 5.2 (`mf:thm:main`). -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- Combined proof of `four_dvd_norm_sharp`: assembles the four independently proved parts. -/
theorem theorem_5_2_sharp_proof :
    IsAlternating ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
      MvPolynomial (Fin 3) ℤ) ∧
    HasOddMonomials ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
      MvPolynomial (Fin 3) ℤ) ∧
    threeTermNorm ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
      MvPolynomial (Fin 3) ℤ) =
      C 6 * X 0 * X 1 * (X 0 - X 1) * (X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2 - X 2 ^ 2) ∧
    ¬ ∃ g : MvPolynomial (Fin 3) ℤ,
      ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
        MvPolynomial (Fin 3) ℤ) = C 2 * g :=
  ⟨sharp_alternating, sharp_oddMonomials, sharp_norm_eq, sharp_not_even⟩

end TernaryPeriodPolynomials.Argument
