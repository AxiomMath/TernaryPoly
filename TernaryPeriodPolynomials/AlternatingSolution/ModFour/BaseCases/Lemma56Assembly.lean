module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Lemma56SymmetricCase
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Lemma56AlternatingCase
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Lemma56UCubed

@[expose] public section


/-! Proof directory: target `modFour_beta_triangular` (`mf:lem:beta`).

Combines `lemma_5_6_symmetric_case` and `lemma_5_6_alternating_case` (the two implications of the
first conjunct, for a symmetric resp. alternating integral lift of `expandOdd r`) with
`uOperator_cubed` (the second conjunct, `U³ = 0`) into exactly the statement of
`Targets/Lemma56.lean`. -/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem lemma_5_6_proof :
    (∀ (r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2)) (v g : MvPolynomial (Fin 3) ℤ),
      reduceTwo v = expandOdd r → threeTermNorm v = C 2 * g →
      (v.IsSymmetric → piOperator (reduceTwo g) = expandOdd (uOperator r)) ∧
      (IsAlternating v → piOperator (reduceTwo g) = expandOdd r + expandOdd (uOperator r))) ∧
    ∀ r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2), uOperator (uOperator (uOperator r)) = 0 :=
  ⟨fun r v g hred hg =>
    ⟨lemma_5_6_symmetric_case r v g hred hg, lemma_5_6_alternating_case r v g hred hg⟩,
   uOperator_cubed⟩

end TernaryPeriodPolynomials.Argument.ModFourBeta
