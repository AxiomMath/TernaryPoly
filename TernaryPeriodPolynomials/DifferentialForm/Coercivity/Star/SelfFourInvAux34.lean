module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvDup
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux34H01
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux34H02
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux34H10
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux34H12
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux34H20
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux34H21

@[expose] public section



/-! First-two-indices-`3,4` slice of the "down-then-up" involution
`star1to4 (star4to1 a) = (1/96) • a` for alternating `a : FourCoordinates`. The six genuinely
pairwise-distinct `(k, l)` branches (`k, l ∈ {0, 1, 2}`, `k ≠ l`) are each discharged by
their own lemma (imported above).



-/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star1to4_star4to1_self_aux34 (a : FourCoordinates) (ha : IsAlternatingFour a)
    (k l : Fin 5) : star1to4 (star4to1 a) 3 4 k l = (1 / 96 : ℝ) • a 3 4 k l := by
  fin_cases k <;> fin_cases l
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux34_01 a ha
  · exact star1to4_star4to1_self_aux34_02 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux34_10 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux34_12 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux34_20 a ha
  · exact star1to4_star4to1_self_aux34_21 a ha
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
