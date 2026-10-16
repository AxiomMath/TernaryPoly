module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleExtension

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G : Type} [Group G]

def twoCocycleCoefficientMap (source target : Rep ℂ G) (linear : source →ₗ[ℂ] target)
    (intertwines : ∀ element vector, linear (source.ρ element vector) = target.ρ element (linear vector))
    (cycle : groupCohomology.cocycles₂ source) : groupCohomology.cocycles₂ target :=
  ⟨fun pair => linear (cycle pair), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro first second third
    have equality := congrArg linear (twoCocycle_relation source cycle first second third)
    simpa only [map_add, intertwines] using equality⟩

theorem twoCocycleCoefficientMap_unit (source target : Rep ℂ G) (linear : source →ₗ[ℂ] target)
    (intertwines : ∀ element vector, linear (source.ρ element vector) = target.ρ element (linear vector))
    (cycle : groupCohomology.cocycles₂ source) (unit_zero : cycle (1, 1) = 0) :
    twoCocycleCoefficientMap source target linear intertwines cycle (1, 1) = 0 := by
  change linear (cycle (1, 1)) = 0
  rw [unit_zero, map_zero]

def twoCocycleExtensionMap (source target : Rep ℂ G) (linear : source →ₗ[ℂ] target)
    (intertwines : ∀ element vector, linear (source.ρ element vector) = target.ρ element (linear vector))
    (cycle : groupCohomology.cocycles₂ source) (unit_zero : cycle (1, 1) = 0) :
    TwoCocycleExtension source cycle unit_zero →*
      TwoCocycleExtension target (twoCocycleCoefficientMap source target linear intertwines cycle)
        (twoCocycleCoefficientMap_unit source target linear intertwines cycle unit_zero) where
  toFun value := ⟨linear value.coefficient, value.element⟩
  map_one' := by
    apply TwoCocycleExtension.ext
    · exact linear.map_zero
    · rfl
  map_mul' first second := by
    apply TwoCocycleExtension.ext
    · change linear (first.coefficient + source.ρ first.element second.coefficient + cycle (first.element, second.element)) =
        linear first.coefficient + target.ρ first.element (linear second.coefficient) + linear (cycle (first.element, second.element))
      rw [map_add, map_add, intertwines]
    · rfl

theorem twoCocycleExtensionMap_injective (source target : Rep ℂ G) (linear : source →ₗ[ℂ] target)
    (intertwines : ∀ element vector, linear (source.ρ element vector) = target.ρ element (linear vector))
    (cycle : groupCohomology.cocycles₂ source) (unit_zero : cycle (1, 1) = 0) (injective : Function.Injective linear) :
    Function.Injective (twoCocycleExtensionMap source target linear intertwines cycle unit_zero) := by
  intro first second equality
  apply TwoCocycleExtension.ext
  · exact injective (congrArg TwoCocycleExtension.coefficient equality)
  · exact congrArg (twoCocycleExtensionProjection target _ _) equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
