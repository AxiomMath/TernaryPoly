module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.EbarReduceTwoForms
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section


open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_q_gen7_pre_collapse :
    Ebar1_D6 * sub₁ (generator 7) + Ebar2_D6 * sub₂ (generator 7) =
    poly_literal% Poly2
      (X 0 * X 1 ^ 4 * X 2 ^ 11 + X 0 * X 1 ^ 6 * X 2 ^ 9 + X 0 * X 1 ^ 10 * X 2 ^ 5 + X 0 * X 1 ^ 12 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 9 + X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 8 + X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 5 + X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 4 + X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 9 + X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 8 + X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 4 + X 0 ^ 3 * X 1 ^ 12 * X 2 + X 0 ^ 4 * X 1 * X 2 ^ 11 + X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 9 + X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 4 + X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 3 + X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 9 + X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 8 + X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 5 + X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 3 + X 0 ^ 6 * X 1 * X 2 ^ 9 + X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 8 + X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 5 + X 0 ^ 6 * X 1 ^ 9 * X 2 + X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 4 + X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 3 + X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 5 + X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 4 + X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 3 + X 0 ^ 9 * X 1 ^ 6 * X 2 + X 0 ^ 10 * X 1 * X 2 ^ 5 + X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 4 + X 0 ^ 12 * X 1 * X 2 ^ 3 + X 0 ^ 12 * X 1 ^ 3 * X 2) := by
  rw [Ebar1_D6_eq_ev, Ebar2_D6_eq_ev, ← ev_generator 7, ev_sub₁, ev_sub₂, ← ev_mulL, ← ev_mulL,
    ← ev_addL]
  refine ev_eq_of_eq (l₂ :=
    [(1, 4, 11), (1, 6, 9), (1, 10, 5), (1, 12, 3), (2, 5, 9), (2, 6, 8), (2, 9, 5), (2, 10, 4),
     (3, 4, 9), (3, 5, 8), (3, 9, 4), (3, 12, 1), (4, 1, 11), (4, 3, 9), (4, 8, 4), (4, 9, 3),
     (5, 2, 9), (5, 3, 8), (5, 6, 5), (5, 8, 3), (6, 1, 9), (6, 2, 8), (6, 5, 5), (6, 9, 1),
     (8, 4, 4), (8, 5, 3), (9, 2, 5), (9, 3, 4), (9, 4, 3), (9, 6, 1), (10, 1, 5), (10, 2, 4),
     (12, 1, 3), (12, 3, 1)]) (by decide +kernel) ?_
  simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
