module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleExtensionMap
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.LiftCommutation

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {G : Type} [Group G]

theorem twoCocycleRealLift_commute_of_one_embedding {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (source : Rep ℂ G) (target : Representation ℂ G E) (linear : source →ₗ[ℂ] E)
    (injective : Function.Injective linear)
    (intertwines : ∀ element vector, linear (source.ρ element vector) = target element (linear vector))
    (cycle : groupCohomology.cocycles₂ source) (unit_zero : cycle (1, 1) = 0)
    (input : Multiplicative ℝ →* G) (operator : Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : operator ^ (cutoff + 1) = 0) (action : ℝ → E →L[ℝ] E)
    (action_eq : ∀ parameter vector, action parameter vector = target (input (Multiplicative.ofAdd parameter)) vector)
    (exponential : ∀ parameter vector, action parameter vector = IsNilpotent.exp ((parameter : ℂ) • operator) vector)
    (lift : Multiplicative ℝ →* TwoCocycleExtension source cycle unit_zero)
    (projects : ∀ element, (lift element).element = input element)
    (regular : DifferentiableAt ℝ (fun parameter => linear (lift (Multiplicative.ofAdd parameter)).coefficient) 0)
    (element : TwoCocycleExtension source cycle unit_zero)
    (base_commutes : ∀ parameter, Commute element.element (input parameter))
    (continuous : Continuous (target element.element))
    (left_regular : DifferentiableAt ℝ (fun parameter => linear (cycle (element.element, input (Multiplicative.ofAdd parameter)))) 0)
    (right_regular : DifferentiableAt ℝ (fun parameter => linear (cycle (input (Multiplicative.ofAdd parameter), element.element))) 0)
    (commutes : Commute element (lift (Multiplicative.ofAdd 1))) :
    ∀ parameter, Commute element (lift parameter) := by
  let mappedCycle := twoCocycleCoefficientMap source (Rep.of target) linear intertwines cycle
  let mappedUnit := twoCocycleCoefficientMap_unit source (Rep.of target) linear intertwines cycle unit_zero
  let mapping := twoCocycleExtensionMap source (Rep.of target) linear intertwines cycle unit_zero
  have mappedCommutes : ∀ parameter, Commute (mapping element) (mapping (lift parameter)) := by
    apply twoCocycleRealLift_commute_of_one target mappedCycle mappedUnit input operator cutoff nilpotent action action_eq
      exponential (mapping.comp lift) projects regular (mapping element) base_commutes continuous left_regular right_regular
    exact commutes.map mapping
  intro parameter
  apply twoCocycleExtensionMap_injective source (Rep.of target) linear intertwines cycle unit_zero injective
  rw [map_mul, map_mul]
  exact (mappedCommutes parameter).eq

end TernaryPeriodPolynomials.SphericalDetection.Helpers
