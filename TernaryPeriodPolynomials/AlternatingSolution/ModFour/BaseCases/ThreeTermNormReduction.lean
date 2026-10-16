module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs

@[expose] public section



/-!
# Naturality of `threeTermNorm` under `reduceTwo`

Reducing an integral polynomial's three-term norm mod two gives exactly the mod-two
norm (`TernaryPoly.CharTwoNorm.norm`) of its reduction. Needed for Lemma 5.5 clauses 1
and 2.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem A1_vec_eq :
    (fun i => MvPolynomial.map (Int.castRingHom (ZMod 2))
        (![(-X 1 : MvPolynomial (Fin 3) ℤ), X 0 - X 1, X 2] i))
      = (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) := by
  funext i
  fin_cases i <;> simp [sub_eq_add_neg, CharTwo.neg_eq]

private theorem A2_vec_eq :
    (fun i => MvPolynomial.map (Int.castRingHom (ZMod 2))
        (![(X 1 - X 0 : MvPolynomial (Fin 3) ℤ), -X 0, X 2] i))
      = (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) := by
  funext i
  fin_cases i <;> simp [sub_eq_add_neg, CharTwo.neg_eq]
  ring

/-- `reduceTwo (threeTermNorm f) = TernaryPoly.CharTwoNorm.norm (reduceTwo f)`. -/
theorem reduceTwo_threeTermNorm (f : MvPolynomial (Fin 3) ℤ) :
    reduceTwo (threeTermNorm f) = TernaryPoly.CharTwoNorm.norm (reduceTwo f) := by
  show MvPolynomial.map (Int.castRingHom (ZMod 2))
      (f + bind₁ ![-X 1, X 0 - X 1, X 2] f + bind₁ ![X 1 - X 0, -X 0, X 2] f)
      = TernaryPoly.CharTwoNorm.norm (MvPolynomial.map (Int.castRingHom (ZMod 2)) f)
  simp only [TernaryPoly.CharTwoNorm.norm, TernaryPoly.CharTwoNorm.sub₁,
    TernaryPoly.CharTwoNorm.sub₂, map_add, MvPolynomial.map_bind₁, A1_vec_eq, A2_vec_eq]

end TernaryPeriodPolynomials.Argument.ModFourBeta
