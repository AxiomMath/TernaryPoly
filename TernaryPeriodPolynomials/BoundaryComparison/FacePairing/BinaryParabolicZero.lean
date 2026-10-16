module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.InnerArithmeticBinaryZero
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ParabolicBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SharpBounds

@[expose] public section


/-!
# The degree-`0` binary parabolic `H¹` is trivial

`binaryParabolicH1 0 = ⊥`: at degree `0` the sharp dimension bound
`finrank ℂ (binaryParabolicH1 degree) + 1 ≤ (degree + 3) / 3`
(`SharpBounds.finrank_binaryParabolicH1_le_sharp`) forces `finrank ℂ (binaryParabolicH1 0) = 0`,
and `CrossedH1 (binaryArithmeticRepresentation 0)` is finite-dimensional
(`ParabolicBounds.level_H1_finiteDimensional 0 (Nat.succ_pos 0)`), so `Submodule.finrank_eq_zero`
upgrades this to the submodule itself vanishing.
-/

noncomputable section

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **The degree-`0` binary parabolic `H¹` is trivial.** -/
theorem binaryParabolicH1_zero_eq_bot :
    binaryParabolicH1 0 = ⊥ := by
  have : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation 0)) :=
    TernaryPeriodPolynomials.LevelThree.ParabolicBounds.level_H1_finiteDimensional 0
      (Nat.succ_pos 0)
  rw [← Submodule.finrank_eq_zero (R := ℂ)]
  have h := TernaryPeriodPolynomials.LevelThree.SharpBounds.finrank_binaryParabolicH1_le_sharp 0
  omega

/-- **The degree-`0` inner bad-line arithmetic binary map is zero.** Combines
`innerBadLineArithmeticBinaryMapZero_parabolic` with the vanishing of the degree-`0` parabolic
submodule. -/
theorem innerBadLineArithmeticBinaryMapZero_eq_zero (coordinate : innerBadLineClasses 0) :
    innerBadLineArithmeticBinaryMapZero coordinate = 0 := by
  have h := innerBadLineArithmeticBinaryMapZero_parabolic coordinate
  rwa [binaryParabolicH1_zero_eq_bot, Submodule.mem_bot] at h

/-- **The degree-`0` inner bad-line classes are trivial.** -/
theorem innerBadLineClasses_zero_eq_bot :
    (⊤ : Submodule ℂ (innerBadLineClasses 0)) = ⊥ := by
  rw [eq_bot_iff]
  intro coordinate _
  rw [Submodule.mem_bot]
  apply innerBadLineArithmeticBinaryMapZero_injective
  rw [innerBadLineArithmeticBinaryMapZero_eq_zero, map_zero]

end TernaryPeriodPolynomials.Argument.FacePairing
