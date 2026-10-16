module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Plane.DomainCancellation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

theorem principalPlaneDomain_pairing_zero
    {sectionValue test : RealSL3 → ℂ} (section_measurable : Measurable sectionValue)
    (test_measurable : Measurable test)
    (section_invariant : ∀ first second matrix,
      sectionValue (realSpecialPlane first second * matrix) = sectionValue matrix)
    (test_periodic : ∀ element : realPlanePeriodSubgroup, ∀ matrix, test (element.val * matrix) = test matrix)
    (test_average_zero : ∀ matrix, (∫ point : ℝ × ℝ,
      test (realSpecialPlane (3 * point.1) (3 * point.2) * matrix) ∂realPlaneUnitMeasure) = 0) :
    (∫ matrix in principalPlaneDomain, sectionValue matrix * star (test matrix) ∂realSpecialLinearHaar) = 0 := by
  by_cases integrable : IntegrableOn (fun matrix => sectionValue matrix * star (test matrix))
      principalPlaneDomain realSpecialLinearHaar
  · refine principalPlaneDomain_integral_zero_of_plane_average
      (function := fun matrix => sectionValue matrix * star (test matrix))
      (section_measurable.mul (continuous_star.measurable.comp test_measurable)) ?_ integrable ?_
    · intro element matrix
      have test_identity := test_periodic element matrix
      obtain ⟨point, represents⟩ := element.property
      rw [test_identity, ← represents]
      change sectionValue (realSpecialPlane _ _ * matrix) * _ = _
      rw [section_invariant]
    · intro matrix
      simp only [section_invariant, integral_const_mul]
      change sectionValue matrix * (∫ point : ℝ × ℝ,
        (starRingEnd ℂ) (test (realSpecialPlane (3 * point.1) (3 * point.2) * matrix)) ∂realPlaneUnitMeasure) = 0
      rw [integral_conj, test_average_zero, map_zero, mul_zero]
  · exact integral_undef integrable

theorem unitaryNormalize_realSpecialIntegralSlice_plane_invariant
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (integral : GL3 IntegralAdeles)
    (first second : ℝ) (matrix : RealSL3) :
    unitaryNormalize degree family parameter
      (realSpecialIntegralSlice integral (realSpecialPlane first second * matrix)) =
      unitaryNormalize degree family parameter (realSpecialIntegralSlice integral matrix) := by
  rw [realSpecialIntegralSlice_left_mul, realSpecialPlane_toGL, atInfinity_planeUnipotent]
  exact unitaryNormalize_unipotent flat.1 parameter _ _ _

theorem normalized_section_residue_average_plane_pairing_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (parameter : ℂ) (integral : GL3 IntegralAdeles) {kernel : RealSL3 → ℂ}
    (kernel_measurable : Measurable kernel) (kernel_integrable : Integrable kernel realSpecialLinearHaar) :
    (∫ matrix in principalPlaneDomain,
      unitaryNormalize degree family parameter (realSpecialIntegralSlice integral matrix) *
        star (normalizedBoundaryResidueAverage degree continuation integral kernel matrix) ∂realSpecialLinearHaar) = 0 := by
  apply principalPlaneDomain_pairing_zero
    ((unitaryNormalize_continuous flat.1 parameter).comp (realSpecialIntegralSlice_continuous integral)).measurable
    (normalizedBoundaryResidueAverage_measurable flat continuation_spec integral kernel_measurable)
    (unitaryNormalize_realSpecialIntegralSlice_plane_invariant flat parameter integral)
  · intro element matrix
    exact normalizedBoundaryResidueAverage_principal_invariant flat continuation_spec integral kernel
      ⟨element.val, (realPlanePeriodSubgroup_le_parabolic element.property).1⟩ matrix
  · exact normalizedBoundaryResidueAverage_plane_average_zero flat continuation_spec integral kernel_integrable

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
