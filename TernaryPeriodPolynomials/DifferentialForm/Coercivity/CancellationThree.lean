module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Mixed.EnergyThree
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentSupport
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDeck
public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.GlobalDivergence

@[expose] public section



/-! Degree-3 global mixed-energy cancellation, mirroring `Cancellation.lean`'s degree-0 argument
via `TernaryPoly.QuotientScalarDescent.integral_divergence_eq_zero`, specialized to the degree-3
TWO cross terms packaged together as `mixedEnergyThree` (unlike degree 0's single term). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The degree-3 current-divergence integral vanishes, mirroring
`integral_compactCurrentDivergenceZero_zero`. -/
theorem integral_compactCurrentDivergenceThree_zero (n : ℕ) (a : Core n 3) :
    ∫ q, compactCurrentDivergenceThree n a q ∂orbitVolume = 0 :=
  TernaryPoly.QuotientScalarDescent.integral_divergence_eq_zero (energyCurrent n 3 a.val.val.val)
    (energyCurrent_compact_smooth n 3 a) (energyCurrent_isDeckVectorField n 3 a.val)
    (energyCurrent_compact_projected_support n 3 a) (compactCurrentDivergenceThree n a)
    (continuous_compactCurrentDivergenceThree n a) (compactCurrentDivergenceThree_coordinateProjection n a)

/-- The degree-3 mixed energy cross terms vanish, mirroring `mixedEnergyZero_zero`. -/
theorem mixedEnergyThree_zero (n : ℕ) (a : Core n 3) : mixedEnergyThree n a = 0 :=
  mixedEnergyThree_eq_zero_of_integral_current_zero n a (integral_compactCurrentDivergenceThree_zero n a)

/-- The degree-3 energy identity with the cross terms eliminated, mirroring
`compact_energy_identity_zero`. -/
theorem compact_energy_identity_three (n : ℕ) (a : Core n 3) :
    ‖inclusion n 4 (compactDifferential (deckRepresentation n) isOpen_univ 3 a)‖ ^ 2 +
      ‖inclusion n 2 (compactAdjoint n 2 a)‖ ^ 2 =
    (‖inclusion n 4 (compactCovariantExterior n 3 a)‖ ^ 2 +
      ‖inclusion n 2 (compactCovariantAdjoint n 2 a)‖ ^ 2) +
    (‖inclusion n 4 (compactSymmetricExterior n 3 a)‖ ^ 2 +
      ‖inclusion n 2 (compactSymmetricContraction n 2 a)‖ ^ 2) := by
  have h := compact_energy_expansion_three n a
  simpa only [mixedEnergyThree_zero n a, mul_zero, add_zero] using h

end TernaryPeriodPolynomials.Argument.Coercivity
