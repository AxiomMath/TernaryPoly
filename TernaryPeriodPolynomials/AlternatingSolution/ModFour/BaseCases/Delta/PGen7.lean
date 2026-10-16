module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.EbarReduceTwoForms
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section



open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_p_gen7_probe : delta_p (generator 7) =
    poly_literal% Poly2
      (X 1 * X 2 ^ 3 * X 0 ^ 10 + X 1 * X 2 ^ 4 * X 0 ^ 9 + X 1 * X 2 ^ 5 * X 0 ^ 8 + X 1 * X 2 ^ 6 * X 0 ^ 7 + X 1 * X 2 ^ 7 * X 0 ^ 6 + X 1 * X 2 ^ 8 * X 0 ^ 5 + X 1 * X 2 ^ 9 * X 0 ^ 4 + X 1 * X 2 ^ 10 * X 0 ^ 3 + X 1 ^ 2 * X 2 ^ 3 * X 0 ^ 9 + X 1 ^ 2 * X 2 ^ 4 * X 0 ^ 8 + X 1 ^ 2 * X 2 ^ 5 * X 0 ^ 7 + X 1 ^ 2 * X 2 ^ 7 * X 0 ^ 5 + X 1 ^ 2 * X 2 ^ 8 * X 0 ^ 4 + X 1 ^ 2 * X 2 ^ 9 * X 0 ^ 3 + X 1 ^ 3 * X 2 * X 0 ^ 10 + X 1 ^ 3 * X 2 ^ 2 * X 0 ^ 9 + X 1 ^ 3 * X 2 ^ 9 * X 0 ^ 2 + X 1 ^ 3 * X 2 ^ 10 * X 0 + X 1 ^ 4 * X 2 * X 0 ^ 9 + X 1 ^ 4 * X 2 ^ 2 * X 0 ^ 8 + X 1 ^ 4 * X 2 ^ 8 * X 0 ^ 2 + X 1 ^ 4 * X 2 ^ 9 * X 0 + X 1 ^ 5 * X 2 * X 0 ^ 8 + X 1 ^ 5 * X 2 ^ 2 * X 0 ^ 7 + X 1 ^ 5 * X 2 ^ 7 * X 0 ^ 2 + X 1 ^ 5 * X 2 ^ 8 * X 0 + X 1 ^ 6 * X 2 * X 0 ^ 7 + X 1 ^ 6 * X 2 ^ 7 * X 0 + X 1 ^ 7 * X 2 * X 0 ^ 6 + X 1 ^ 7 * X 2 ^ 2 * X 0 ^ 5 + X 1 ^ 7 * X 2 ^ 5 * X 0 ^ 2 + X 1 ^ 7 * X 2 ^ 6 * X 0 + X 1 ^ 8 * X 2 * X 0 ^ 5 + X 1 ^ 8 * X 2 ^ 2 * X 0 ^ 4 + X 1 ^ 8 * X 2 ^ 4 * X 0 ^ 2 + X 1 ^ 8 * X 2 ^ 5 * X 0 + X 1 ^ 9 * X 2 * X 0 ^ 4 + X 1 ^ 9 * X 2 ^ 2 * X 0 ^ 3 + X 1 ^ 9 * X 2 ^ 3 * X 0 ^ 2 + X 1 ^ 9 * X 2 ^ 4 * X 0 + X 1 ^ 10 * X 2 * X 0 ^ 3 + X 1 ^ 10 * X 2 ^ 3 * X 0) := by
  refine delta_p_eq_of_reflect (ev_generator 7).symm (lQ :=
    [(1, 3, 10), (1, 4, 9), (1, 5, 8), (1, 6, 7), (1, 7, 6), (1, 8, 5), (1, 9, 4), (1, 10, 3),
     (2, 3, 9), (2, 4, 8), (2, 5, 7), (2, 7, 5), (2, 8, 4), (2, 9, 3), (3, 1, 10), (3, 2, 9),
     (3, 9, 2), (3, 10, 1), (4, 1, 9), (4, 2, 8), (4, 8, 2), (4, 9, 1), (5, 1, 8), (5, 2, 7),
     (5, 7, 2), (5, 8, 1), (6, 1, 7), (6, 7, 1), (7, 1, 6), (7, 2, 5), (7, 5, 2), (7, 6, 1),
     (8, 1, 5), (8, 2, 4), (8, 4, 2), (8, 5, 1), (9, 1, 4), (9, 2, 3), (9, 3, 2), (9, 4, 1),
     (10, 1, 3), (10, 3, 1)]) ?_ ?_
  · simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
