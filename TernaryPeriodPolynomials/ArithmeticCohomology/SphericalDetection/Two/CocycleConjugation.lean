module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RelativeTwoCocycleNormalization

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G : Type} [Group G]

/-- The usual mixed cochain gives the inner-conjugation homotopy in degree two. -/
def conjugationTwoCocycleHomotopy (representation : Rep ℂ G) (element : G)
    (cycle : groupCohomology.cocycles₂ representation) : G → representation :=
  fun argument => cycle (element, element⁻¹ * argument * element) - cycle (argument, element)

theorem conjugationTwoCocycleHomotopy_boundary (representation : Rep ℂ G) (element : G)
    (cycle : groupCohomology.cocycles₂ representation) (first second : G) :
    twoBoundaryCycle representation (conjugationTwoCocycleHomotopy representation element cycle) (first, second) =
      representation.ρ element (cycle (element⁻¹ * first * element, element⁻¹ * second * element)) -
        cycle (first, second) := by
  have first_equation := twoCocycle_relation representation cycle element
    (element⁻¹ * first * element) (element⁻¹ * second * element)
  have second_equation := twoCocycle_relation representation cycle first element
    (element⁻¹ * second * element)
  have third_equation := twoCocycle_relation representation cycle first second element
  simp only [mul_assoc, mul_inv_cancel_left] at first_equation second_equation
  rw [twoBoundaryCycle_apply]
  simp only [conjugationTwoCocycleHomotopy, map_sub, mul_assoc]
  linear_combination (norm := abel) first_equation - second_equation + third_equation

variable {A W : Type} [CommGroup A] [AddCommGroup W]

theorem abelianTwoCocycleAlternation_mul (cycle : A × A → W)
    (relation : ∀ first second third, cycle (first * second, third) + cycle (first, second) =
      cycle (second, third) + cycle (first, second * third)) (first second third : A) :
    cycle (first * second, third) - cycle (third, first * second) =
      (cycle (first, third) - cycle (third, first)) + (cycle (second, third) - cycle (third, second)) := by
  have equation0 := relation first second third
  have equation1 := relation first third second
  have equation2 := relation third first second
  rw [mul_comm second third] at equation0
  rw [mul_comm third first] at equation2
  linear_combination (norm := abel) equation0 - equation1 + equation2

theorem abelianTwoCocycleAlternation_one (cycle : A × A → W)
    (relation : ∀ first second third, cycle (first * second, third) + cycle (first, second) =
      cycle (second, third) + cycle (first, second * third)) (element : A) :
    cycle (1, element) - cycle (element, 1) = 0 := by
  have equation := abelianTwoCocycleAlternation_mul cycle relation 1 1 element
  simp only [one_mul] at equation
  linear_combination (norm := abel) -equation

theorem abelianTwoCocycleAlternation_inv (cycle : A × A → W)
    (relation : ∀ first second third, cycle (first * second, third) + cycle (first, second) =
      cycle (second, third) + cycle (first, second * third)) (first second : A) :
    cycle (first⁻¹, second⁻¹) - cycle (second⁻¹, first⁻¹) = cycle (first, second) - cycle (second, first) := by
  have equation0 := abelianTwoCocycleAlternation_mul cycle relation first first⁻¹ second⁻¹
  have equation1 := abelianTwoCocycleAlternation_mul cycle relation second second⁻¹ first
  simp only [mul_inv_cancel, abelianTwoCocycleAlternation_one cycle relation] at equation0 equation1
  linear_combination (norm := abel) -equation0 - equation1

variable [Module ℂ W]

/-- An inversion conjugator acting by minus one kills the projected radical alternation. -/
theorem twoCocycle_projected_alternation_zero (inclusion : A →* G) (representation : Rep ℂ G)
    (projection : representation →ₗ[ℂ] W)
    (radical_trivial : ∀ radical vector, projection (representation.ρ (inclusion radical) vector) = projection vector)
    (element : G) (conjugates : ∀ radical, element⁻¹ * inclusion radical * element = inclusion radical⁻¹)
    (negates : ∀ vector, projection (representation.ρ element vector) = -projection vector)
    (cycle : groupCohomology.cocycles₂ representation) (first second : A) :
    projection (cycle (inclusion first, inclusion second) - cycle (inclusion second, inclusion first)) = 0 := by
  let projected : A × A → W := fun pair => projection (cycle (inclusion pair.1, inclusion pair.2))
  have relation (left middle right : A) : projected (left * middle, right) + projected (left, middle) =
      projected (middle, right) + projected (left, middle * right) := by
    have equation := congrArg projection (twoCocycle_relation representation cycle (inclusion left) (inclusion middle) (inclusion right))
    simpa only [map_add, radical_trivial, projected, map_mul] using equation
  have inverse := abelianTwoCocycleAlternation_inv projected relation first second
  have equation0 := congrArg projection (conjugationTwoCocycleHomotopy_boundary representation element cycle (inclusion first) (inclusion second))
  have equation1 := congrArg projection (conjugationTwoCocycleHomotopy_boundary representation element cycle (inclusion second) (inclusion first))
  simp only [twoBoundaryCycle_apply, map_add, map_sub, radical_trivial, negates, conjugates] at equation0 equation1
  rw [← map_mul, mul_comm first second, map_mul] at equation0
  dsimp only [projected] at inverse
  rw [map_sub]
  have twice : (2 : ℂ) • (projection (cycle (inclusion first, inclusion second)) -
      projection (cycle (inclusion second, inclusion first))) = 0 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]
    linear_combination (norm := abel) equation0 - equation1 - inverse
  exact (smul_eq_zero.mp twice).resolve_left (by norm_num)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
