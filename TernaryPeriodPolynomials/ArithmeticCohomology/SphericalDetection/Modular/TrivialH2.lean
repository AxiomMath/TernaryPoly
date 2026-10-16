module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.Lifting
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CentralCocycleTorsion
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CohomologyEdge

@[expose] public section


open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem modularTrivialCocycle_boundary (representation : Rep ℂ (SpecialLinearGroup (Fin 2) ℤ))
    (trivial : ∀ element vector, representation.ρ element vector = vector)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0) :
    ∃ primitive : SpecialLinearGroup (Fin 2) ℤ → representation,
      ∀ first second, representation.ρ first (primitive second) - primitive (first * second) + primitive first =
        cycle (first, second) := by
  have sixth : modularOrderSix ^ 6 = 1 := by
    calc
      modularOrderSix ^ 6 = (modularOrderSix ^ 3) ^ 2 := by rw [← pow_mul]
      _ = (ModularGroup.S ^ 2) ^ 2 := by rw [modularOrderSix_cube]
      _ = ModularGroup.S ^ 4 := by rw [← pow_mul]
      _ = 1 := modularOrderFour
  obtain ⟨first, first_image, fourth⟩ := twoCocycleExtension_torsion_lift representation cycle unit_zero
    trivial ModularGroup.S 4 (by decide) modularOrderFour
  obtain ⟨second, second_image, sixth⟩ := twoCocycleExtension_torsion_lift representation cycle unit_zero
    trivial modularOrderSix 6 (by decide) sixth
  have relation : second ^ 3 = first ^ 2 := by
    refine twoCocycleExtension_torsion_lift_unique representation cycle unit_zero trivial
      (second ^ 3) (first ^ 2) ?_ 2 (by decide) ?_ ?_
    · rw [map_pow, map_pow, first_image, second_image, modularOrderSix_cube]
    · simpa only [← pow_mul] using sixth
    · simpa only [← pow_mul] using fourth
  let splitting := modularLiftSection (twoCocycleExtensionProjection representation cycle unit_zero)
    first second first_image second_image fourth relation
  refine ⟨fun element => -(splitting element).coefficient, ?_⟩
  exact twoCocycleExtension_section_boundary representation cycle unit_zero splitting
    (modularLiftSection_projection (twoCocycleExtensionProjection representation cycle unit_zero)
      first second first_image second_image fourth relation)

/-- Complex degree-two cohomology of SL2(Z) vanishes for every trivial coefficient representation. -/
theorem modularTrivialH2_zero (representation : Rep ℂ (SpecialLinearGroup (Fin 2) ℤ))
    (trivial : ∀ element vector, representation.ρ element vector = vector)
    (cohomology : groupCohomology.H2 representation) : cohomology = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective representation cohomology
  rw [← unitNormalizedTwoCocycle_H2]
  rw [groupCohomology.H2π_eq_zero_iff]
  obtain ⟨primitive, boundary⟩ := modularTrivialCocycle_boundary representation trivial
    (unitNormalizedTwoCocycle representation cycle) (unitNormalizedTwoCocycle_unit representation cycle)
  refine ⟨primitive, ?_⟩
  funext pair
  exact boundary pair.1 pair.2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
