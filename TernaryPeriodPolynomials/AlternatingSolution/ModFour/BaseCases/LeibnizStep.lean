module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs

@[expose] public section



/-!
# The Leibniz step for `β`

If an integral polynomial `D` satisfies `Aᵢ(D) = D + 2 Eᵢ` for `i = 1, 2` (the two
substitutions appearing in `threeTermNorm`), and `threeTermNorm v = 2 g`, then
`threeTermNorm (D * v) = 2 * (D * g + E₁ * A₁(v) + E₂ * A₂(v))`.

This is the generic engine behind the "Leibniz reduction" for Lemma 5.6: multiplying
`v` by a Dickson lift `D` changes `β(v)` by a computable first-order defect, rather
than requiring a fresh direct computation of `threeTermNorm` for every multiplier.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-- The first substitution appearing in `threeTermNorm`. -/
noncomputable abbrev A1vec : Fin 3 → MvPolynomial (Fin 3) ℤ := ![-X 1, X 0 - X 1, X 2]

/-- The second substitution appearing in `threeTermNorm`. -/
noncomputable abbrev A2vec : Fin 3 → MvPolynomial (Fin 3) ℤ := ![X 1 - X 0, -X 0, X 2]

/-- **Leibniz step.** If `D` is an integral lift with known defects `E₁, E₂` under the
two `threeTermNorm` substitutions, and `threeTermNorm v = 2 g`, then
`threeTermNorm (D * v) = 2 * (D * g + E₁ * A₁(v) + E₂ * A₂(v))`. -/
theorem leibniz_step {D E1 E2 v g : MvPolynomial (Fin 3) ℤ}
    (h1 : bind₁ A1vec D = D + C 2 * E1) (h2 : bind₁ A2vec D = D + C 2 * E2)
    (hg : threeTermNorm v = C 2 * g) :
    threeTermNorm (D * v) =
      C 2 * (D * g + E1 * bind₁ A1vec v + E2 * bind₁ A2vec v) := by
  simp only [threeTermNorm, map_mul] at hg ⊢
  linear_combination D * hg + bind₁ A1vec v * h1 + bind₁ A2vec v * h2

end TernaryPeriodPolynomials.Argument.ModFourBeta
