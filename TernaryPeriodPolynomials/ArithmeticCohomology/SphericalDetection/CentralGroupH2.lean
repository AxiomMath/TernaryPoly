module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CohomologyEdge

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G : Type} [Group G]

def centralTwoCocycleHomotopy (representation : Rep ℂ G) (central : G)
    (cycle : groupCohomology.cocycles₂ representation) : G → representation :=
  fun element => cycle (central, element) - cycle (element, central)

theorem centralTwoCocycleHomotopy_boundary (representation : Rep ℂ G) (central : G)
    (commutes : ∀ element, central * element = element * central)
    (cycle : groupCohomology.cocycles₂ representation) (first second : G) :
    twoBoundaryCycle representation (centralTwoCocycleHomotopy representation central cycle) (first, second) =
      representation.ρ central (cycle (first, second)) - cycle (first, second) := by
  have first_equation := twoCocycle_relation representation cycle central first second
  have second_equation := twoCocycle_relation representation cycle first central second
  have third_equation := twoCocycle_relation representation cycle first second central
  rw [commutes first] at first_equation
  rw [commutes second] at second_equation
  rw [twoBoundaryCycle_apply]
  simp only [centralTwoCocycleHomotopy, map_sub]
  linear_combination (norm := abel) first_equation - second_equation + third_equation

theorem groupH2_zero_of_central_scalar (representation : Rep ℂ G) (central : G)
    (commutes : ∀ element, central * element = element * central) (scalar : ℂ)
    (nontrivial : scalar ≠ 1) (action : ∀ vector, representation.ρ central vector = scalar • vector)
    (cohomology : groupCohomology.H2 representation) : cohomology = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective representation cohomology
  rw [groupCohomology.H2π_eq_zero_iff]
  let homotopy := centralTwoCocycleHomotopy representation central cycle
  refine ⟨fun element => (scalar - 1)⁻¹ • homotopy element, ?_⟩
  funext pair
  change representation.ρ pair.1 ((scalar - 1)⁻¹ • homotopy pair.2) -
    (scalar - 1)⁻¹ • homotopy (pair.1 * pair.2) + (scalar - 1)⁻¹ • homotopy pair.1 = cycle (pair.1, pair.2)
  rw [map_smul, ← smul_sub, ← smul_add]
  change (scalar - 1)⁻¹ • twoBoundaryCycle representation homotopy (pair.1, pair.2) = cycle (pair.1, pair.2)
  rw [centralTwoCocycleHomotopy_boundary representation central commutes, action]
  have difference : scalar • cycle (pair.1, pair.2) - cycle (pair.1, pair.2) =
      (scalar - 1) • cycle (pair.1, pair.2) := by rw [sub_smul, one_smul]
  rw [difference, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr nontrivial), one_smul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
