module

public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.GlobalDivergence
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.DifferentialLower
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentSupport

@[expose] public section


/-! Actual global mixed-energy cancellation and positive-degree differential coercivity. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormCoordinates PolynomialFormHilbert
  PolynomialFormConnection SymmetricSpaceRiemannian SmoothCoveringDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian

theorem integral_compactCurrentDivergence_zero (n : ℕ) (a : Core n 2) :
    ∫ q, compactCurrentDivergence n a q ∂orbitVolume = 0 :=
  QuotientScalarDescent.integral_divergence_eq_zero (energyCurrent n 2 a.val.val.val)
    (energyCurrent_compact_smooth n 2 a) (energyCurrent_isDeckVectorField n 2 a.val)
    (energyCurrent_compact_projected_support n 2 a) (compactCurrentDivergence n a)
    (continuous_compactCurrentDivergence n a) (compactCurrentDivergence_coordinateProjection n a)

theorem mixedEnergy_zero (n : ℕ) (a : Core n 2) : mixedEnergy n a = 0 :=
  mixedEnergy_eq_zero_of_integral_current_zero n a (integral_compactCurrentDivergence_zero n a)

theorem compact_energy_identity (n : ℕ) (a : Core n 2) :
    ‖inclusion n 3 (compactDifferential (deckRepresentation n) isOpen_univ 2 a)‖ ^ 2 +
      ‖inclusion n 1 (compactAdjoint n 1 a)‖ ^ 2 =
    (‖inclusion n 3 (compactCovariantExterior n 2 a)‖ ^ 2 +
      ‖inclusion n 1 (compactCovariantAdjoint n 1 a)‖ ^ 2) +
    (‖inclusion n 3 (compactSymmetricExterior n 2 a)‖ ^ 2 +
      ‖inclusion n 1 (compactSymmetricContraction n 1 a)‖ ^ 2) := by
  have h := compact_energy_expansion n a
  simpa only [mixedEnergy_zero n a, mul_zero, add_zero] using h

theorem norm_differential_energy_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c > 0, ∀ a : Core n 2,
      c * ‖inclusion n 2 a‖ ^ 2 ≤
        ‖inclusion n 1 (compactAdjoint n 1 a)‖ ^ 2 +
          ‖inclusion n 3 (compactDifferential (deckRepresentation n) isOpen_univ 2 a)‖ ^ 2 :=
  norm_differential_energy_coercive_of_mixedEnergy_zero hn (mixedEnergy_zero n)

end TernaryPoly.PolynomialFormGeometricEnergy
