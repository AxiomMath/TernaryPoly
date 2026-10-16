module

public import TernaryPeriodPolynomials.AlternatingSolution.Lemma55

@[expose] public section


/-!
# Lemma 5.5 (`mf:lem:well-defined`) as a single unconditional statement

Formalized by Claude Sonnet 5.5.

Paper: Lemma 5.5 and its proof.
The target `modFour_beta_wellDefined` takes, in its fourth clause, the evenness of `N(P(D²) v)` as a hypothesis
(`threeTermNorm (evalSquaredLift P * v) = C 2 * g'`).  The paper's proof ("Consequently, the integral squares of
the three polynomials in `mf:eq:invariants` are invariant modulo four under the substitutions in `N` ... Multiplying a lift by any
polynomial in those squares therefore commutes with division of its norm by two followed by reduction and application of `Π`")
uses exactly this invariance to pass the evenness through the multiplication: it does not display the computation, but
"commutes with division of its norm by two" presupposes that the scaled norm is even.  That computation is
`Statements.Lemma55.threeTermNorm_evalSquaredLift_mul_even` (from `Proofs/ModFourBeta/SquaredLiftInvariance.lean`), so the hypothesis of
the clause is dispensable.

`lemma_5_5_unconditional` is the four clauses of the target with clause 4 strengthened to conclude the evenness: for every integral
`P` in three variables and every integral `v` with `N v = 2 g`, the polynomial `N(P(D₄²,D₆²,D₇²) v)` is `2 g'` for some `g'`, and every
such `g'` satisfies `Π (g' mod 2) = P(D²) Π (g mod 2)`.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.Statements.Lemma55

open TernaryPeriodPolynomials.Argument

/-- **Lemma 5.5, unconditional form.**  (1) symmetric and alternating integral lifts of every `v = ∑ r_j(p,q,ρ) L_j` exist and their norms
are even; (2) `β_±` is independent of the choice of lift (of the same symmetry type); (3) `β_±` is additive; (4) multiplication of a
lift by a polynomial in the squares of the integral Dickson invariants keeps the norm even and multiplies `β_±` by the reduction of
that polynomial (`R₂`-linearity). -/
theorem lemma_5_5_unconditional :
    (∀ r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2),
      (∃ v g : MvPolynomial (Fin 3) ℤ, v.IsSymmetric ∧ reduceTwo v = expandOdd r ∧
        threeTermNorm v = C 2 * g) ∧
      (∃ v g : MvPolynomial (Fin 3) ℤ, IsAlternating v ∧ reduceTwo v = expandOdd r ∧
        threeTermNorm v = C 2 * g)) ∧
    (∀ v v' g g' : MvPolynomial (Fin 3) ℤ,
      ((v.IsSymmetric ∧ v'.IsSymmetric) ∨ (IsAlternating v ∧ IsAlternating v')) →
      reduceTwo v = reduceTwo v' → threeTermNorm v = C 2 * g → threeTermNorm v' = C 2 * g' →
      piOperator (reduceTwo g) = piOperator (reduceTwo g')) ∧
    (∀ v v' g g' : MvPolynomial (Fin 3) ℤ,
      threeTermNorm v = C 2 * g → threeTermNorm v' = C 2 * g' →
      threeTermNorm (v + v') = C 2 * (g + g') ∧
      piOperator (reduceTwo (g + g')) = piOperator (reduceTwo g) + piOperator (reduceTwo g')) ∧
    (∀ P v g : MvPolynomial (Fin 3) ℤ, threeTermNorm v = C 2 * g →
      (∃ g', threeTermNorm (evalSquaredLift P * v) = C 2 * g') ∧
      ∀ g', threeTermNorm (evalSquaredLift P * v) = C 2 * g' →
        piOperator (reduceTwo g') = reduceTwo (evalSquaredLift P) * piOperator (reduceTwo g)) :=
  ⟨modFour_beta_wellDefined.1, modFour_beta_wellDefined.2.1, modFour_beta_wellDefined.2.2.1, fun P v g hv => lemma_5_5_clause4_complete P v g hv⟩

end TernaryPeriodPolynomials.Argument.Statements.Lemma55
