module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.ReduceTwoBasic

@[expose] public section



/-! Naturality of `threeTermNorm` under reduction mod two: `reduceTwo` carries
`threeTermNorm` to `TernaryPoly.CharTwoNorm.norm`. -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

private theorem sub1_tuple_eq :
    (fun i : Fin 3 => MvPolynomial.map (Int.castRingHom (ZMod 2))
      ((![-X 1, X 0 - X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℤ) i))
      = (![X 1, X 0 + X 1, X 2] : Fin 3 → TernaryPoly.CharTwoNorm.Poly) := by
  funext i
  fin_cases i <;>
    simp [map_neg, MvPolynomial.map_X, sub_eq_add_neg, neg_eq_self_two]

private theorem sub2_tuple_eq :
    (fun i : Fin 3 => MvPolynomial.map (Int.castRingHom (ZMod 2))
      ((![X 1 - X 0, -X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) ℤ) i))
      = (![X 0 + X 1, X 0, X 2] : Fin 3 → TernaryPoly.CharTwoNorm.Poly) := by
  funext i
  fin_cases i <;>
    simp [map_neg, MvPolynomial.map_X, sub_eq_add_neg, neg_eq_self_two, add_comm]

/-- Reduction mod two carries `threeTermNorm` to `TernaryPoly.CharTwoNorm.norm`. -/
theorem reduceTwo_threeTermNorm (f : MvPolynomial (Fin 3) ℤ) :
    reduceTwo (threeTermNorm f) = TernaryPoly.CharTwoNorm.norm (reduceTwo f) := by
  show MvPolynomial.map (Int.castRingHom (ZMod 2))
      (f + bind₁ ![-X 1, X 0 - X 1, X 2] f + bind₁ ![X 1 - X 0, -X 0, X 2] f) = _
  rw [map_add, map_add, MvPolynomial.map_bind₁, MvPolynomial.map_bind₁, sub1_tuple_eq,
    sub2_tuple_eq]
  rfl

end TernaryPeriodPolynomials.Argument
