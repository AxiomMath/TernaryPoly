module

public import TernaryPeriodPolynomials.AlternatingSolution.TriangularCalculation
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.SquaredLiftInvariance

@[expose] public section


/-!
# Lemma 5.5 with the evenness of the scaled norm as a conclusion

In the proof of `mf:lem:well-defined` the paper notes that the integral squares of the
invariants `mf:eq:invariants` are invariant modulo four under the substitutions of `N`, so that
multiplying a lift by a polynomial in those squares commutes with halving its norm. The target `modFour_beta_wellDefined` (clause 4) takes the evenness of `N(P(D²) v)` as a hypothesis. Here it is
proved: if `N v = 2 g`, then `N(P(D²) v) = 2 g'` for an explicit `g'`, and the clause-4 identity
`Π (g' mod 2) = P(D²) Π (g mod 2)` follows.

Written by Claude Opus 5.5.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.Statements.Lemma55

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ModFourBeta

/-- If `N v = 2 g`, then `N(P(D₄², D₆², D₇²) v)` is even, with an explicit half. -/
theorem threeTermNorm_evalSquaredLift_mul_even (P v g : MvPolynomial (Fin 3) ℤ)
    (hv : threeTermNorm v = C 2 * g) :
    ∃ g', threeTermNorm (evalSquaredLift P * v) = C 2 * g' := by
  obtain ⟨e₁, he₁⟩ := mod_four_evalSquaredLift_A1 P
  obtain ⟨e₂, he₂⟩ := mod_four_evalSquaredLift_A2 P
  refine ⟨evalSquaredLift P * g + 2 * (e₁ * bind₁ ![-X 1, X 0 - X 1, X 2] v
    + e₂ * bind₁ ![X 1 - X 0, -X 0, X 2] v), ?_⟩
  have hN : threeTermNorm v = v + bind₁ ![-X 1, X 0 - X 1, X 2] v
      + bind₁ ![X 1 - X 0, -X 0, X 2] v := rfl
  have h2 : (C 2 : MvPolynomial (Fin 3) ℤ) = 2 := rfl
  rw [hN, h2] at hv
  simp only [threeTermNorm, map_mul, he₁, he₂, h2]
  linear_combination (evalSquaredLift P) * hv

/-- **Lemma 5.5, clause 4, with the evenness concluded.** If `N v = 2 g`, there is `g'` with
`N(P(D²) v) = 2 g'`, and every such `g'` satisfies `Π (g' mod 2) = P(D²) Π (g mod 2)`. -/
theorem lemma_5_5_clause4_complete (P v g : MvPolynomial (Fin 3) ℤ)
    (hv : threeTermNorm v = C 2 * g) :
    (∃ g', threeTermNorm (evalSquaredLift P * v) = C 2 * g') ∧
    ∀ g', threeTermNorm (evalSquaredLift P * v) = C 2 * g' →
      piOperator (reduceTwo g') = reduceTwo (evalSquaredLift P) * piOperator (reduceTwo g) :=
  ⟨threeTermNorm_evalSquaredLift_mul_even P v g hv,
    fun g' hg' => modFour_beta_wellDefined.2.2.2 P v g g' hv hg'⟩

end TernaryPeriodPolynomials.Argument.Statements.Lemma55
