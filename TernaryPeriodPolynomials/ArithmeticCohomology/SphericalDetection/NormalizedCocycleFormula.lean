module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleUnits

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem unitNormalizedTwoCocycle_apply {G : Type} [Group G] (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₂ representation) (first second : G) :
    unitNormalizedTwoCocycle representation cycle (first, second) = cycle (first, second) - cycle (first, 1) := by
  change cycle (first, second) - twoBoundaryCycle representation (fun _ => cycle (1, 1)) (first, second) = _
  rw [twoBoundaryCycle_apply, sub_add_cancel]
  rw [twoCocycle_one_right representation cycle first]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
