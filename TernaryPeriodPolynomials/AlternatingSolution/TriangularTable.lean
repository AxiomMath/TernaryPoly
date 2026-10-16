module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Lemma56Assembly

@[expose] public section


/-! Target: Lemma 5.6 (`mf:lem:beta`) of the paper. -/

open MvPolynomial

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Lemma 5.6.** On the odd reduced norm kernel `v = ∑_j r_j(p,q,ρ) L_j`,
`β₊(v) = U(v)` and `β₋(v) = v + U(v)`, computed with any symmetric, respectively alternating,
integral lift. Moreover `U³ = 0`. -/
theorem modFour_beta_triangular :
    (∀ (r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2)) (v g : MvPolynomial (Fin 3) ℤ),
      reduceTwo v = expandOdd r → threeTermNorm v = C 2 * g →
      (v.IsSymmetric → piOperator (reduceTwo g) = expandOdd (uOperator r)) ∧
      (IsAlternating v → piOperator (reduceTwo g) = expandOdd r + expandOdd (uOperator r))) ∧
    ∀ r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2), uOperator (uOperator (uOperator r)) = 0 := by
  exact TernaryPeriodPolynomials.Argument.ModFourBeta.lemma_5_6_proof

end TernaryPeriodPolynomials
