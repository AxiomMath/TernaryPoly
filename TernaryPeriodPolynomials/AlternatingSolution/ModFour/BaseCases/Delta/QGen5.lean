module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.EbarReduceTwoForms
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section



open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_q_gen5_probe : delta_q (generator 5) =
    poly_literal% Poly2
      (X 1 * X 2 ^ 3 * X 0 ^ 10 + X 1 * X 2 ^ 6 * X 0 ^ 7 + X 1 * X 2 ^ 7 * X 0 ^ 6 + X 1 * X 2 ^ 10 * X 0 ^ 3 + X 1 ^ 3 * X 2 * X 0 ^ 10 + X 1 ^ 3 * X 2 ^ 4 * X 0 ^ 7 + X 1 ^ 3 * X 2 ^ 7 * X 0 ^ 4 + X 1 ^ 3 * X 2 ^ 10 * X 0 + X 1 ^ 4 * X 2 ^ 3 * X 0 ^ 7 + X 1 ^ 4 * X 2 ^ 7 * X 0 ^ 3 + X 1 ^ 6 * X 2 * X 0 ^ 7 + X 1 ^ 6 * X 2 ^ 7 * X 0 + X 1 ^ 7 * X 2 * X 0 ^ 6 + X 1 ^ 7 * X 2 ^ 3 * X 0 ^ 4 + X 1 ^ 7 * X 2 ^ 4 * X 0 ^ 3 + X 1 ^ 7 * X 2 ^ 6 * X 0 + X 1 ^ 10 * X 2 * X 0 ^ 3 + X 1 ^ 10 * X 2 ^ 3 * X 0) := by
  refine delta_q_eq_of_reflect (ev_generator 5).symm (lQ :=
    [(1, 3, 10), (1, 6, 7), (1, 7, 6), (1, 10, 3), (3, 1, 10), (3, 4, 7), (3, 7, 4), (3, 10, 1),
     (4, 3, 7), (4, 7, 3), (6, 1, 7), (6, 7, 1), (7, 1, 6), (7, 3, 4), (7, 4, 3), (7, 6, 1),
     (10, 1, 3), (10, 3, 1)]) ?_ ?_
  · simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
