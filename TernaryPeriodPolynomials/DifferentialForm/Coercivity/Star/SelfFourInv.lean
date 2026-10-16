module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvDup
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux01
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux02
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux03
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux04
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux12
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux13
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux14
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux23
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux24
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux34
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourSwap

@[expose] public section



/-! Full involution `star1to4 (star4to1 a) = (1/96) • a` for alternating `a : FourCoordinates`,
assembled from: the duplicate-index shortcut (`StarSelfFourInvDup`), the ten `i < j` slices
(`StarSelfFourInvAuxIJ`), and `star1to4_swap01` together with `IsAlternatingFour`'s first
clause (`StarSelfFourSwap`) for the ten `i > j` slices. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star1to4_star4to1_self (a : FourCoordinates) (ha : IsAlternatingFour a)
    (i j k l : Fin 5) : star1to4 (star4to1 a) i j k l = (1 / 96 : ℝ) • a i j k l := by
  fin_cases i <;> fin_cases j
  -- Each of the 25 branches
  -- below is resolved by exactly one direct tactic, in the fixed order `fin_cases i <;> fin_cases
  -- j` produces: `i = 0, 1, 2, 3, 4`, and for each, `j = 0, 1, 2, 3, 4`.
  -- i = 0
  · exact star1to4_star4to1_self_of_dup ha (Or.inl rfl)                                  -- j = 0
  · exact star1to4_star4to1_self_aux01 a ha k l                                          -- j = 1
  · exact star1to4_star4to1_self_aux02 a ha k l                                          -- j = 2
  · exact star1to4_star4to1_self_aux03 a ha k l                                          -- j = 3
  · exact star1to4_star4to1_self_aux04 a ha k l                                          -- j = 4
  -- i = 1
  · exact star1to4_star4to1_self_of_swap ha k l (star1to4_star4to1_self_aux01 a ha k l)  -- j = 0
  · exact star1to4_star4to1_self_of_dup ha (Or.inl rfl)                                  -- j = 1
  · exact star1to4_star4to1_self_aux12 a ha k l                                          -- j = 2
  · exact star1to4_star4to1_self_aux13 a ha k l                                          -- j = 3
  · exact star1to4_star4to1_self_aux14 a ha k l                                          -- j = 4
  -- i = 2
  · exact star1to4_star4to1_self_of_swap ha k l (star1to4_star4to1_self_aux02 a ha k l)  -- j = 0
  · exact star1to4_star4to1_self_of_swap ha k l (star1to4_star4to1_self_aux12 a ha k l)  -- j = 1
  · exact star1to4_star4to1_self_of_dup ha (Or.inl rfl)                                  -- j = 2
  · exact star1to4_star4to1_self_aux23 a ha k l                                          -- j = 3
  · exact star1to4_star4to1_self_aux24 a ha k l                                          -- j = 4
  -- i = 3
  · exact star1to4_star4to1_self_of_swap ha k l (star1to4_star4to1_self_aux03 a ha k l)  -- j = 0
  · exact star1to4_star4to1_self_of_swap ha k l (star1to4_star4to1_self_aux13 a ha k l)  -- j = 1
  · exact star1to4_star4to1_self_of_swap ha k l (star1to4_star4to1_self_aux23 a ha k l)  -- j = 2
  · exact star1to4_star4to1_self_of_dup ha (Or.inl rfl)                                  -- j = 3
  · exact star1to4_star4to1_self_aux34 a ha k l                                          -- j = 4
  -- i = 4
  · exact star1to4_star4to1_self_of_swap ha k l (star1to4_star4to1_self_aux04 a ha k l)  -- j = 0
  · exact star1to4_star4to1_self_of_swap ha k l (star1to4_star4to1_self_aux14 a ha k l)  -- j = 1
  · exact star1to4_star4to1_self_of_swap ha k l (star1to4_star4to1_self_aux24 a ha k l)  -- j = 2
  · exact star1to4_star4to1_self_of_swap ha k l (star1to4_star4to1_self_aux34 a ha k l)  -- j = 3
  · exact star1to4_star4to1_self_of_dup ha (Or.inl rfl)                                  -- j = 4

end TernaryPeriodPolynomials.Argument.Coercivity
