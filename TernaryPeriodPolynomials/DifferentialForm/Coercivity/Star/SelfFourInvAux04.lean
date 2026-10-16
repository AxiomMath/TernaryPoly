module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvDup
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux04H12
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux04H13
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux04H21
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux04H23
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux04H31
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux04H32

@[expose] public section



/-! First-two-indices-`0,4` slice of the "down-then-up" involution
`star1to4 (star4to1 a) = (1/96) • a` for alternating `a : FourCoordinates`. The six genuinely
pairwise-distinct `(k, l)` branches (`k, l ∈ {1, 2, 3}`, `k ≠ l`) are each discharged by
their own lemma (imported above).



-/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star1to4_star4to1_self_aux04 (a : FourCoordinates) (ha : IsAlternatingFour a)
    (k l : Fin 5) : star1to4 (star4to1 a) 0 4 k l = (1 / 96 : ℝ) • a 0 4 k l := by
  fin_cases k <;> fin_cases l
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux04_12 a ha
  · exact star1to4_star4to1_self_aux04_13 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux04_21 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux04_23 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux04_31 a ha
  · exact star1to4_star4to1_self_aux04_32 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide

end TernaryPeriodPolynomials.Argument.Coercivity
