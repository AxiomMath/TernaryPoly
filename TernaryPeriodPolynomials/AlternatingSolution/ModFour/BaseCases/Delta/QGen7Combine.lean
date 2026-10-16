module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QGen7PiCleanBatchA
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QGen7PiCleanBatchB
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section


open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_q_gen7 : delta_q (generator 7) =
    poly_literal% Poly2
      (X 1 * X 2 ^ 3 * X 0 ^ 12 + X 1 * X 2 ^ 5 * X 0 ^ 10 + X 1 * X 2 ^ 6 * X 0 ^ 9 + X 1 * X 2 ^ 7 * X 0 ^ 8 + X 1 * X 2 ^ 8 * X 0 ^ 7 + X 1 * X 2 ^ 9 * X 0 ^ 6 + X 1 * X 2 ^ 10 * X 0 ^ 5 + X 1 * X 2 ^ 12 * X 0 ^ 3 + X 1 ^ 2 * X 2 ^ 4 * X 0 ^ 10 + X 1 ^ 2 * X 2 ^ 6 * X 0 ^ 8 + X 1 ^ 2 * X 2 ^ 8 * X 0 ^ 6 + X 1 ^ 2 * X 2 ^ 10 * X 0 ^ 4 + X 1 ^ 3 * X 2 * X 0 ^ 12 + X 1 ^ 3 * X 2 ^ 4 * X 0 ^ 9 + X 1 ^ 3 * X 2 ^ 9 * X 0 ^ 4 + X 1 ^ 3 * X 2 ^ 12 * X 0 + X 1 ^ 4 * X 2 ^ 2 * X 0 ^ 10 + X 1 ^ 4 * X 2 ^ 3 * X 0 ^ 9 + X 1 ^ 4 * X 2 ^ 5 * X 0 ^ 7 + X 1 ^ 4 * X 2 ^ 7 * X 0 ^ 5 + X 1 ^ 4 * X 2 ^ 9 * X 0 ^ 3 + X 1 ^ 4 * X 2 ^ 10 * X 0 ^ 2 + X 1 ^ 5 * X 2 * X 0 ^ 10 + X 1 ^ 5 * X 2 ^ 4 * X 0 ^ 7 + X 1 ^ 5 * X 2 ^ 7 * X 0 ^ 4 + X 1 ^ 5 * X 2 ^ 10 * X 0 + X 1 ^ 6 * X 2 * X 0 ^ 9 + X 1 ^ 6 * X 2 ^ 2 * X 0 ^ 8 + X 1 ^ 6 * X 2 ^ 8 * X 0 ^ 2 + X 1 ^ 6 * X 2 ^ 9 * X 0 + X 1 ^ 7 * X 2 * X 0 ^ 8 + X 1 ^ 7 * X 2 ^ 4 * X 0 ^ 5 + X 1 ^ 7 * X 2 ^ 5 * X 0 ^ 4 + X 1 ^ 7 * X 2 ^ 8 * X 0 + X 1 ^ 8 * X 2 * X 0 ^ 7 + X 1 ^ 8 * X 2 ^ 2 * X 0 ^ 6 + X 1 ^ 8 * X 2 ^ 6 * X 0 ^ 2 + X 1 ^ 8 * X 2 ^ 7 * X 0 + X 1 ^ 9 * X 2 * X 0 ^ 6 + X 1 ^ 9 * X 2 ^ 3 * X 0 ^ 4 + X 1 ^ 9 * X 2 ^ 4 * X 0 ^ 3 + X 1 ^ 9 * X 2 ^ 6 * X 0 + X 1 ^ 10 * X 2 * X 0 ^ 5 + X 1 ^ 10 * X 2 ^ 2 * X 0 ^ 4 + X 1 ^ 10 * X 2 ^ 4 * X 0 ^ 2 + X 1 ^ 10 * X 2 ^ 5 * X 0 + X 1 ^ 12 * X 2 * X 0 ^ 3 + X 1 ^ 12 * X 2 ^ 3 * X 0) := by
  refine delta_q_eq_of_reflect (ev_generator 7).symm (lQ :=
    [(1, 3, 12), (1, 5, 10), (1, 6, 9), (1, 7, 8), (1, 8, 7), (1, 9, 6), (1, 10, 5), (1, 12, 3),
     (2, 4, 10), (2, 6, 8), (2, 8, 6), (2, 10, 4), (3, 1, 12), (3, 4, 9), (3, 9, 4), (3, 12, 1),
     (4, 2, 10), (4, 3, 9), (4, 5, 7), (4, 7, 5), (4, 9, 3), (4, 10, 2), (5, 1, 10), (5, 4, 7),
     (5, 7, 4), (5, 10, 1), (6, 1, 9), (6, 2, 8), (6, 8, 2), (6, 9, 1), (7, 1, 8), (7, 4, 5),
     (7, 5, 4), (7, 8, 1), (8, 1, 7), (8, 2, 6), (8, 6, 2), (8, 7, 1), (9, 1, 6), (9, 3, 4),
     (9, 4, 3), (9, 6, 1), (10, 1, 5), (10, 2, 4), (10, 4, 2), (10, 5, 1), (12, 1, 3), (12, 3, 1)]) ?_ ?_
  · simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
