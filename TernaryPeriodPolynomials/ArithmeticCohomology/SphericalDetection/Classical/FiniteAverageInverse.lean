module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.FiniteAverageAnalytic
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspClassicalFiniteAverageFamily_eventually_isUnit (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ) (negative : halfWeight < 0)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (convergent : 3 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re) :
    ∀ᶠ exponent : ℂ in nhds ((degree : ℂ) / 2 + 3 + cohomologicalPoint),
      IsUnit (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent) := by
  let : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) :=
    cuspClassicalVectors_finiteDimensional cusp central_positive halfWeight negative
  exact (cuspClassicalFiniteAverageFamily_analyticAt cusp central_positive halfWeight negative _ convergent).continuousAt
    ((Units.isOpen (R := cuspClassicalVectors cusp halfWeight →L[ℂ] cuspClassicalVectors cusp halfWeight)).mem_nhds
      (cuspClassicalFiniteAverageFamily_endpoint_isUnit cusp central_positive
      spherical_cusp large cohomological halfWeight negative weight convergent))

theorem cuspClassicalFiniteAverageFamily_inverse_analyticAt (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ) (negative : halfWeight < 0)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (convergent : 3 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re) :
    AnalyticAt ℂ (fun exponent => Ring.inverse
      (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent))
        ((degree : ℂ) / 2 + 3 + cohomologicalPoint) := by
  let : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) :=
    cuspClassicalVectors_finiteDimensional cusp central_positive halfWeight negative
  obtain ⟨unit, unit_value⟩ := cuspClassicalFiniteAverageFamily_endpoint_isUnit cusp central_positive
    spherical_cusp large cohomological halfWeight negative weight convergent
  have analytic : AnalyticAt ℂ Ring.inverse
      (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
        ((degree : ℂ) / 2 + 3 + cohomologicalPoint)) := by
    rw [← unit_value]
    exact analyticAt_inverse (𝕜 := ℂ)
      (A := cuspClassicalVectors cusp halfWeight →L[ℂ] cuspClassicalVectors cusp halfWeight) unit
  exact analytic.comp
    (cuspClassicalFiniteAverageFamily_analyticAt cusp central_positive halfWeight negative _ convergent)

theorem cuspClassicalFiniteAverageFamily_inverse_cancel (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ) (negative : halfWeight < 0)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (convergent : 3 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re) :
    ∀ᶠ exponent : ℂ in nhds ((degree : ℂ) / 2 + 3 + cohomologicalPoint),
      Ring.inverse (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent) *
        cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent = 1 ∧
      cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent *
        Ring.inverse (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent) = 1 := by
  filter_upwards [cuspClassicalFiniteAverageFamily_eventually_isUnit cusp central_positive spherical_cusp large
    cohomological halfWeight negative weight convergent] with exponent unit
  exact ⟨Ring.inverse_mul_cancel _ unit, Ring.mul_inverse_cancel _ unit⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
