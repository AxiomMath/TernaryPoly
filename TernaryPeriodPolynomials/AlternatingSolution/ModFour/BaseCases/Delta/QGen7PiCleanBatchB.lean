module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QGen7PreCollapse
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.PiOperatorSplit


public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QGen7PiCleanBatchA
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section


open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_q_gen7_pi_clean_batchB :
    ((piSubstitutions.drop 9).map fun t => bind₁ t
      (poly_literal% (MvPolynomial (Fin 3) (ZMod 2))
        (X 0 * X 1 ^ 4 * X 2 ^ 11 + X 0 * X 1 ^ 6 * X 2 ^ 9 + X 0 * X 1 ^ 10 * X 2 ^ 5 + X 0 * X 1 ^ 12 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 9 + X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 8 + X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 5 + X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 4 + X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 9 + X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 8 + X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 4 + X 0 ^ 3 * X 1 ^ 12 * X 2 + X 0 ^ 4 * X 1 * X 2 ^ 11 + X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 9 + X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 4 + X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 3 + X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 9 + X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 8 + X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 5 + X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 3 + X 0 ^ 6 * X 1 * X 2 ^ 9 + X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 8 + X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 5 + X 0 ^ 6 * X 1 ^ 9 * X 2 + X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 4 + X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 3 + X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 5 + X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 4 + X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 3 + X 0 ^ 9 * X 1 ^ 6 * X 2 + X 0 ^ 10 * X 1 * X 2 ^ 5 + X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 4 + X 0 ^ 12 * X 1 * X 2 ^ 3 + X 0 ^ 12 * X 1 ^ 3 * X 2))).sum =
    poly_literal% (MvPolynomial (Fin 3) (ZMod 2))
      (X 0 * X 1 ^ 3 * X 2 ^ 12 + X 0 * X 1 ^ 4 * X 2 ^ 11 + X 0 * X 1 ^ 5 * X 2 ^ 10 + X 0 * X 1 ^ 6 * X 2 ^ 9 + X 0 * X 1 ^ 9 * X 2 ^ 6 + X 0 * X 1 ^ 10 * X 2 ^ 5 + X 0 * X 1 ^ 11 * X 2 ^ 4 + X 0 * X 1 ^ 12 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 6 + X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 2 + X 0 ^ 3 * X 1 * X 2 ^ 12 + X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 9 + X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 5 + X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 11 + X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 10 + X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 4 + X 0 ^ 4 * X 1 ^ 11 * X 2 + X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 5 + X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 4 + X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 2 + X 0 ^ 5 * X 1 ^ 10 * X 2 + X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 5 + X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 4 + X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 2 + X 0 ^ 6 * X 1 ^ 9 * X 2 + X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 6 + X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 5 + X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 4 + X 0 ^ 8 * X 1 ^ 7 * X 2 + X 0 ^ 9 * X 1 * X 2 ^ 6 + X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 3 + X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 2 + X 0 ^ 9 * X 1 ^ 6 * X 2 + X 0 ^ 10 * X 1 * X 2 ^ 5 + X 0 ^ 10 * X 1 ^ 5 * X 2) := by
  refine piDrop_eq_of_reflect 9 (lP :=
    [(1, 4, 11), (1, 6, 9), (1, 10, 5), (1, 12, 3), (2, 5, 9), (2, 6, 8), (2, 9, 5), (2, 10, 4),
     (3, 4, 9), (3, 5, 8), (3, 9, 4), (3, 12, 1), (4, 1, 11), (4, 3, 9), (4, 8, 4), (4, 9, 3),
     (5, 2, 9), (5, 3, 8), (5, 6, 5), (5, 8, 3), (6, 1, 9), (6, 2, 8), (6, 5, 5), (6, 9, 1),
     (8, 4, 4), (8, 5, 3), (9, 2, 5), (9, 3, 4), (9, 4, 3), (9, 6, 1), (10, 1, 5), (10, 2, 4),
     (12, 1, 3), (12, 3, 1)]) (lQ :=
    [(1, 3, 12), (1, 4, 11), (1, 5, 10), (1, 6, 9), (1, 9, 6), (1, 10, 5), (1, 11, 4), (1, 12, 3),
     (2, 8, 6), (2, 12, 2), (3, 1, 12), (3, 4, 9), (3, 8, 5), (3, 9, 4), (4, 1, 11), (4, 2, 10),
     (4, 8, 4), (4, 11, 1), (5, 6, 5), (5, 7, 4), (5, 9, 2), (5, 10, 1), (6, 5, 5), (6, 6, 4),
     (6, 8, 2), (6, 9, 1), (8, 2, 6), (8, 3, 5), (8, 4, 4), (8, 7, 1), (9, 1, 6), (9, 4, 3),
     (9, 5, 2), (9, 6, 1), (10, 1, 5), (10, 5, 1)]) ?_ ?_ ?_
  · simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
