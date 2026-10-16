module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AltExtensionFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.FourOne
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.OneFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesA
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesB

@[expose] public section



/-! The "repeated index" case of the "down-then-up" involution
`star1to4 (star4to1 a) = (1/96) • a` for alternating `a : FourCoordinates`: whenever two of the four free indices coincide,
both sides vanish identically, with NO need to unfold `star4to1` or substitute `altFour` at all.
The left side vanishes because `star1to4`'s own definition is a single sum against
`eps5 i j k l m`, already zero (one of the ten `eps5_eq_zero_XY` lemmas, fired symbolically on
the repeated pair) regardless of the summand `star4to1 a m`, which is therefore never unfolded.
The right side vanishes by the matching `alternatingFour_diagXY` lemma. This disposes of 505 of
the 625 raw `(i, j, k, l)` quadruples (fully symbolic, no `fin_cases`), leaving only the
120 pairwise-distinct quadruples to the `altFour`-substitution route. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star1to4_star4to1_self_of_dup {a : FourCoordinates} (ha : IsAlternatingFour a)
    {i j k l : Fin 5} (h : i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l) :
    star1to4 (star4to1 a) i j k l = (1 / 96 : ℝ) • a i j k l := by
  have hL : star1to4 (star4to1 a) i j k l = 0 := by
    rcases h with h | h | h | h | h | h <;> rw [h] <;> simp [star1to4]
  have hR : a i j k l = 0 := by
    rcases h with h | h | h | h | h | h
    · rw [h]; exact alternatingFour_diag01 ha j k l
    · rw [h]; exact alternatingFour_diag02 ha k j l
    · rw [h]; exact alternatingFour_diag03 ha l j k
    · rw [h]; exact alternatingFour_diag12 ha i k l
    · rw [h]; exact alternatingFour_diag13 ha i l k
    · rw [h]; exact alternatingFour_diag23 ha i j l
  rw [hL, hR, smul_zero]

end TernaryPeriodPolynomials.Argument.Coercivity
