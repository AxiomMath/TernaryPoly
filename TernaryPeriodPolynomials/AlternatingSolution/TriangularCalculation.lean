module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Lemma55Assembly

@[expose] public section


/-! Target: Lemma 5.5 (`mf:lem:well-defined`) and the existence of lifts used to define
`β_±` in equation `mf:eq:beta`. -/

open MvPolynomial

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Lemma 5.5.** For `v = ∑_j r_j(p,q,ρ) L_j` as in `mf:eq:eight`, symmetric and alternating
integral lifts exist, and their norms are even. The maps
`β_±(v) = Π((N ṽ^±)/2 mod 2)` are independent of the respective choices of lift and are
`R₂`-linear, where `R₂ = k[p², q², ρ]` is lifted by the squared integral polynomials of
`mf:eq:invariants`. -/
theorem modFour_beta_wellDefined :
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
  TernaryPeriodPolynomials.Argument.ModFourBeta.lemma_5_5_assembled

end TernaryPeriodPolynomials
