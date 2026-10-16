module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RelativeTwoCocycleNormalization

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G : Type} [Group G]

theorem twoCocycle_one_left (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation)
    (element : G) : cycle (1, element) = cycle (1, 1) := by
  have equation := twoCocycle_relation representation cycle 1 1 element
  simp only [one_mul, map_one, Module.End.one_apply] at equation
  linear_combination (norm := abel) -equation

theorem twoCocycle_one_right (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation)
    (element : G) : cycle (element, 1) = representation.ρ element (cycle (1, 1)) := by
  have equation := twoCocycle_relation representation cycle element 1 1
  simp only [mul_one] at equation
  linear_combination (norm := abel) equation

def unitNormalizedTwoCocycle (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation) :
    groupCohomology.cocycles₂ representation :=
  cycle - twoBoundaryCycle representation (fun _ => cycle (1, 1))

theorem unitNormalizedTwoCocycle_unit (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation) :
    unitNormalizedTwoCocycle representation cycle (1, 1) = 0 := by
  change cycle (1, 1) - twoBoundaryCycle representation (fun _ => cycle (1, 1)) (1, 1) = 0
  rw [twoBoundaryCycle_apply, map_one, Module.End.one_apply]
  abel

theorem unitNormalizedTwoCocycle_H2 (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation) :
    groupCohomology.H2π representation (unitNormalizedTwoCocycle representation cycle) =
      groupCohomology.H2π representation cycle := by
  unfold unitNormalizedTwoCocycle
  rw [map_sub, twoBoundaryCycle_H2_zero, sub_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
