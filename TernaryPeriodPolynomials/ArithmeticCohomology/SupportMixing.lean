module

public import TernaryPeriodPolynomials.Polynomial.Defs

@[expose] public section


/-!
# The support-mixing example of the paper

Formalized by Claude Haiku 5.5.

The paper's `eq:support-mixing-example` reads `y²z ↦ (x−y)²z = x²z − 2xyz + y²z`, where the
arrow is the substitution `(Af)(x,y,z) = f(-y, x-y, z)` of the norm relation. In the definitions this operator is the second summand of `threeTermNorm`
(`Revision/Defs/Polynomial.lean`), written `bind₁ ![-X 1, X 0 - X 1, X 2]`. The two statements below
are literal identities of `MvPolynomial (Fin 3) R`, for an arbitrary commutative ring `R`
(in particular `R = ℤ` and `R = ℚ`).
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

variable {R : Type*} [CommRing R]

/-- **Support-mixing example (`eq:support-mixing-example`).** Under the substitution `A`
of the norm relation, `y²z` goes to `(x−y)²z`, and this equals `x²z − 2xyz + y²z`. -/
theorem support_mixing_example :
    bind₁ ![-X 1, X 0 - X 1, X 2] (X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) R) =
        (X 0 - X 1) ^ 2 * X 2 ∧
      bind₁ ![-X 1, X 0 - X 1, X 2] (X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) R) =
        X 0 ^ 2 * X 2 - 2 * X 0 * X 1 * X 2 + X 1 ^ 2 * X 2 := by
  constructor
  · simp
  · simp
    ring

/-- The same substitution, read off the operator `threeTermNorm`: the second summand of the
norm of `y²z` is `(x−y)²z`, the third is `x²z` (from `(A²f)(x,y,z) = f(y−x,−x,z)`), so the norm of
`y²z` is `2(x²z − xyz + y²z)`. -/
theorem threeTermNorm_support_mixing :
    threeTermNorm (X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) R) =
      2 * (X 0 ^ 2 * X 2 - X 0 * X 1 * X 2 + X 1 ^ 2 * X 2) := by
  simp only [threeTermNorm]
  simp
  ring

end TernaryPeriodPolynomials.Argument.Identities
