module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BinaryParabolicZero
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineVacuityZero
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.GoodFlagTransport

@[expose] public section


/-!
# Inner line classes vanish at `n = 0`

Final assembly of the degree-`0` vacuity of `face_pairing_perfect`: an `InnerBoundary` line class
`b` at `n = 0` has vanishing good-flag cusp residue (`cuspRes_line_true_eq_zero_atZero`), hence
vanishes on every good flag (`vanishesOnGood_of_cuspRes_good_eq_zero`), hence lies in
`innerBadLineClasses 0`, which is trivial (`innerBadLineClasses_zero_eq_bot`, via the degree-`0`
parabolic vanishing). So there is no nonzero such class.

Original work by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing

/-- **Degree-`0` vacuity.** Every `InnerBoundary` line class at `n = 0` is zero. -/
theorem eq_zero_of_innerBoundary_atZero {b : StratumH2 0 trivialCharacter .line}
    (inner : InnerBoundary 0 trivialCharacter .line b) : b = 0 := by
  have hgood : VanishesOnGood 0 trivialCharacter .line b :=
    GoodPlaneSpan.vanishesOnGood_of_cuspRes_good_eq_zero b
      (cuspRes_line_true_eq_zero_atZero inner)
  have hmem : b ∈ innerBadLineClasses 0 := (mem_innerBadLineClasses_iff 0 b).mpr ⟨hgood, inner⟩
  have hbot : (⟨b, hmem⟩ : innerBadLineClasses 0) ∈ (⊥ : Submodule ℂ (innerBadLineClasses 0)) := by
    rw [← innerBadLineClasses_zero_eq_bot]
    trivial
  exact congrArg Subtype.val ((Submodule.mem_bot ℂ).mp hbot)

end TernaryPeriodPolynomials.Argument.FacePairing
