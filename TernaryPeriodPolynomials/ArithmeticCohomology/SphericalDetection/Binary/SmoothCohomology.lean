module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Cohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SmoothFamilies

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cohomological_exists_smooth_nonzero_H1 {degree : ℕ}
    {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree),
      groupCohomology.H1π (binaryCuspidalRep cusp degree) cycle ≠ 0 ∧
      Smooth (fun point : Fin 2 → BinaryRealGL => fun position =>
        (binarySmoothCoordinates cusp basis
          (binaryRightTranslation cusp degree (atInfinity (point 1)) (cycle (point 0)))
          position).val) := by
  rcases cohomological with ⟨cycle, cuspidal, smooth_lifts, _, cocycle, nonboundary⟩
  refine ⟨binaryCocycleToGroupCocycle cusp cycle cuspidal cocycle, ?_, ?_⟩
  · exact fun zero => nonboundary
      ((binaryCocycleToGroupCocycle_H1_zero_iff cusp cycle cuspidal cocycle).mp zero)
  · apply binarySmoothCoordinates_smooth
    exact smooth_lifts

end TernaryPeriodPolynomials.SphericalDetection.Helpers
