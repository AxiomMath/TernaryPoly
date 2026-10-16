module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Mixed.EnergyDegreeFour
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentSupport
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDeck
public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.GlobalDivergence

@[expose] public section



/-! Degree-4 global mixed-energy cancellation, mirroring `CancellationThree.lean`'s degree-3
argument one level up via `TernaryPoly.QuotientScalarDescent.integral_divergence_eq_zero`,
specialized to the degree-4 TWO cross terms packaged together as `mixedEnergyDegreeFour`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The degree-4 current-divergence integral vanishes, mirroring
`integral_compactCurrentDivergenceThree_zero`. -/
theorem integral_compactCurrentDivergenceDegreeFour_zero (n : ℕ) (a : Core n 4) :
    ∫ q, compactCurrentDivergenceDegreeFour n a q ∂orbitVolume = 0 :=
  TernaryPoly.QuotientScalarDescent.integral_divergence_eq_zero (energyCurrent n 4 a.val.val.val)
    (energyCurrent_compact_smooth n 4 a) (energyCurrent_isDeckVectorField n 4 a.val)
    (energyCurrent_compact_projected_support n 4 a) (compactCurrentDivergenceDegreeFour n a)
    (continuous_compactCurrentDivergenceDegreeFour n a)
    (compactCurrentDivergenceDegreeFour_coordinateProjection n a)

/-- The degree-4 mixed energy cross terms vanish, mirroring `mixedEnergyThree_zero`. -/
theorem mixedEnergyDegreeFour_zero (n : ℕ) (a : Core n 4) : mixedEnergyDegreeFour n a = 0 :=
  mixedEnergyDegreeFour_eq_zero_of_integral_current_zero n a
    (integral_compactCurrentDivergenceDegreeFour_zero n a)

/-- The degree-4 energy identity with the cross terms eliminated, mirroring
`compact_energy_identity_three`. -/
theorem compact_energy_identity_degree_four (n : ℕ) (a : Core n 4) :
    ‖inclusion n 5 (compactDifferential (deckRepresentation n) isOpen_univ 4 a)‖ ^ 2 +
      ‖inclusion n 3 (compactAdjoint n 3 a)‖ ^ 2 =
    (‖inclusion n 5 (compactCovariantExterior n 4 a)‖ ^ 2 +
      ‖inclusion n 3 (compactCovariantAdjoint n 3 a)‖ ^ 2) +
    (‖inclusion n 5 (compactSymmetricExterior n 4 a)‖ ^ 2 +
      ‖inclusion n 3 (compactSymmetricContraction n 3 a)‖ ^ 2) := by
  have h := compact_energy_expansion_degree_four n a
  simpa only [mixedEnergyDegreeFour_zero n a, mul_zero, add_zero] using h

end TernaryPeriodPolynomials.Argument.Coercivity
