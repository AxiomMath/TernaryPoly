module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.OperatorAdditivity

@[expose] public section



/-!
# Lemma 5.5, clause 3 (additivity of `β` in `v`)

Mechanical: `threeTermNorm` is a sum of `AlgHom`s so is additive, and `piOperator` is
additive (`piOperator_add`, imported from `ModFourMain.OperatorAdditivity`).
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem threeTermNorm_add (p q : MvPolynomial (Fin 3) ℤ) :
    threeTermNorm (p + q) = threeTermNorm p + threeTermNorm q := by
  simp only [threeTermNorm, map_add]
  ring

/-- **Lemma 5.5, clause 3** (additivity). -/
theorem lemma_5_5_clause3 :
    ∀ v v' g g' : MvPolynomial (Fin 3) ℤ,
      threeTermNorm v = C 2 * g → threeTermNorm v' = C 2 * g' →
      threeTermNorm (v + v') = C 2 * (g + g') ∧
      piOperator (reduceTwo (g + g')) = piOperator (reduceTwo g) + piOperator (reduceTwo g') := by
  intro v v' g g' hv hv'
  refine ⟨?_, by rw [map_add, piOperator_add]⟩
  rw [threeTermNorm_add, hv, hv']
  ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
