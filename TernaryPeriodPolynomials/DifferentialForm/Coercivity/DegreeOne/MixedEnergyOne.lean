module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.MixedOperatorOne
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.ScalarPairingOne
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Splitting
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.IntegratedAlgebra

@[expose] public section



noncomputable section
namespace TernaryPeriodPolynomials.Argument.CoercivityOne

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise ContDiff

/-- The exact two mixed pairings at degree 1, mirroring `mixedEnergyThree` one level down. Named
`geomMixedEnergyOne` to avoid colliding with the algebraic `mixedEnergyOne` of `CasimirOne.lean`. -/
def geomMixedEnergyOne (n : ℕ) (a : Core n 1) : ℝ :=
  inner ℝ (inclusion n 2 (compactCovariantExterior n 1 a)) (inclusion n 2 (compactSymmetricExterior n 1 a)) +
  inner ℝ (inclusion n 0 (compactCovariantAdjoint n 0 a)) (inclusion n 0 (compactSymmetricContraction n 0 a))

/-- Degree-1 energy expansion, mirroring `compact_energy_expansion_three` one level down. -/
theorem compact_energy_expansion_one (n : ℕ) (a : Core n 1) :
    ‖inclusion n 2 (compactDifferential (deckRepresentation n) isOpen_univ 1 a)‖ ^ 2 +
      ‖inclusion n 0 (compactAdjoint n 0 a)‖ ^ 2 =
    (‖inclusion n 2 (compactCovariantExterior n 1 a)‖ ^ 2 +
      ‖inclusion n 0 (compactCovariantAdjoint n 0 a)‖ ^ 2) +
    (‖inclusion n 2 (compactSymmetricExterior n 1 a)‖ ^ 2 +
      ‖inclusion n 0 (compactSymmetricContraction n 0 a)‖ ^ 2) + 2 * geomMixedEnergyOne n a :=
  (congrArg₂ (fun u v => ‖u‖ ^ 2 + ‖v‖ ^ 2) (inclusion_flat_sum n 1 a) (inclusion_adjoint_sum n 0 a)).trans
    (norm_pair_add_expansion _ _ _ _)

/-- `geomMixedEnergyOne` as a Hilbert pairing against the compact mixed operator, mirroring
`mixedEnergyThree_eq_inner_compactMixedOperatorThree` one level down. -/
theorem geomMixedEnergyOne_eq_inner_compactMixedOperatorOne (n : ℕ) (a : Core n 1) :
    geomMixedEnergyOne n a = inner ℝ (inclusion n 1 a) (inclusion n 1 (compactMixedOperatorOne n a)) := by
  have h1 : inner ℝ (inclusion n 2 (compactCovariantExterior n 1 a))
      (inclusion n 2 (compactSymmetricExterior n 1 a)) =
      inner ℝ (inclusion n 1 a) (inclusion n 1 (compactSymmetricContraction n 1 (compactCovariantExterior n 1 a))) :=
    (real_inner_comm _ _).trans (inner_symmetricExterior_one n a (compactCovariantExterior n 1 a))
  have h2 : inner ℝ (inclusion n 0 (compactCovariantAdjoint n 0 a))
      (inclusion n 0 (compactSymmetricContraction n 0 a)) =
      inner ℝ (inclusion n 1 a) (inclusion n 1 (compactCovariantExterior n 0 (compactSymmetricContraction n 0 a))) :=
    (real_inner_comm _ _).trans ((inner_covariantExterior_zero n (compactSymmetricContraction n 0 a) a).symm.trans
      (real_inner_comm _ _))
  exact (congrArg₂ (· + ·) h1 h2).trans ((inner_add_right _ _ _).symm.trans
    (congrArg (inner ℝ (inclusion n 1 a)) ((inclusion n 1).map_add _ _).symm))

theorem geomMixedEnergyOne_eq_integral (n : ℕ) (a : Core n 1) :
    geomMixedEnergyOne n a = ∫ q, scalarPairing n 1 a.val (compactMixedOperatorOne n a).val q ∂orbitVolume :=
  (geomMixedEnergyOne_eq_inner_compactMixedOperatorOne n a).trans
    (inner_inclusion n 1 a (compactMixedOperatorOne n a))

theorem integral_compactCurrentDivergenceOne_eq (n : ℕ) (a : Core n 1) :
    (∫ q, compactCurrentDivergenceOne n a q ∂orbitVolume) = 2 * geomMixedEnergyOne n a :=
  (integral_const_mul 2 _).trans (congrArg (2 * ·) (geomMixedEnergyOne_eq_integral n a).symm)

theorem geomMixedEnergyOne_eq_zero_of_integral_current_zero (n : ℕ) (a : Core n 1)
    (h : (∫ q, compactCurrentDivergenceOne n a q ∂orbitVolume) = 0) : geomMixedEnergyOne n a = 0 := by
  have hz := (integral_compactCurrentDivergenceOne_eq n a).symm.trans h
  linarith

end TernaryPeriodPolynomials.Argument.CoercivityOne
