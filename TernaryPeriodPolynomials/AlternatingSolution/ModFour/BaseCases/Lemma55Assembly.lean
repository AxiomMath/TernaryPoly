module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.ExplicitLiftConstruction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.LiftIndependence
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.OperatorAdditivityBeta
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.SquaredLiftInvariance

@[expose] public section



/-!
# Lemma 5.5 — assembly of all four clauses

`lemma_5_5_clause1` (existence, `ExplicitLiftConstruction.lean`), `lemma_5_5_clause2`
(lift independence, `LiftIndependence.lean`), `lemma_5_5_clause3` (additivity,
`OperatorAdditivityBeta.lean`), and `lemma_5_5_clause4` (`R₂`-linearity,
`SquaredLiftInvariance.lean`) are each proved separately; this file packages them into the
exact four-way conjunction of the target `modFour_beta_wellDefined`.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-- **Lemma 5.5**, fully assembled from its four clauses. -/
theorem lemma_5_5_assembled :
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
    (∀ P v g g' : MvPolynomial (Fin 3) ℤ, threeTermNorm v = C 2 * g →
      threeTermNorm (evalSquaredLift P * v) = C 2 * g' →
      piOperator (reduceTwo g') = reduceTwo (evalSquaredLift P) * piOperator (reduceTwo g)) :=
  ⟨lemma_5_5_clause1, lemma_5_5_clause2, lemma_5_5_clause3, lemma_5_5_clause4⟩

end TernaryPeriodPolynomials.Argument.ModFourBeta
