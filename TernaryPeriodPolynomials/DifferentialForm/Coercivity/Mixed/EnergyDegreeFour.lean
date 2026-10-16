module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Mixed.OperatorDegreeFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ScalarPairingFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CovariantAdjointThree
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Splitting

@[expose] public section



/-! Degree-4 specialization of the mixed-energy cross term (TWO surviving terms), mirroring
`MixedEnergyThree.lean` one level up: the "upper" cross term uses `inner_symmetricExterior_four`
(`ScalarPairingFour.lean`) and the "lower" one uses `inner_covariantExterior_three`
(`CovariantAdjointThree.lean`). Named with the `DegreeFour`/bare-`_four` mix already established by
`AnticommutatorDegreeFour.lean`/`MixedOperatorDegreeFour.lean`: `compact_energy_expansion_four` and
`compact_energy_identity_four` already belong to the degree-5 pipeline (`MixedEnergyFour.lean`/
`CoercivityFour.lean`, for `a : Core n 5`), so this file's two analogous names are suffixed
`_degree_four` instead to avoid collision. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The exact two mixed pairings at degree 4, mirroring `mixedEnergyThree` one level up. -/
def mixedEnergyDegreeFour (n : ℕ) (a : Core n 4) : ℝ :=
  inner ℝ (inclusion n 5 (compactCovariantExterior n 4 a)) (inclusion n 5 (compactSymmetricExterior n 4 a)) +
  inner ℝ (inclusion n 3 (compactCovariantAdjoint n 3 a)) (inclusion n 3 (compactSymmetricContraction n 3 a))

/-- Degree-4 energy expansion, mirroring `compact_energy_expansion_three` one level up. -/
theorem compact_energy_expansion_degree_four (n : ℕ) (a : Core n 4) :
    ‖inclusion n 5 (compactDifferential (deckRepresentation n) isOpen_univ 4 a)‖ ^ 2 +
      ‖inclusion n 3 (compactAdjoint n 3 a)‖ ^ 2 =
    (‖inclusion n 5 (compactCovariantExterior n 4 a)‖ ^ 2 +
      ‖inclusion n 3 (compactCovariantAdjoint n 3 a)‖ ^ 2) +
    (‖inclusion n 5 (compactSymmetricExterior n 4 a)‖ ^ 2 +
      ‖inclusion n 3 (compactSymmetricContraction n 3 a)‖ ^ 2) + 2 * mixedEnergyDegreeFour n a :=
  (congrArg₂ (fun u v => ‖u‖ ^ 2 + ‖v‖ ^ 2) (inclusion_flat_sum n 4 a) (inclusion_adjoint_sum n 3 a)).trans
    (norm_pair_add_expansion _ _ _ _)

/-- `mixedEnergyDegreeFour` as a Hilbert pairing against the compact mixed operator, mirroring
`mixedEnergyThree_eq_inner_compactMixedOperatorThree`. -/
theorem mixedEnergyDegreeFour_eq_inner_compactMixedOperatorDegreeFour (n : ℕ) (a : Core n 4) :
    mixedEnergyDegreeFour n a =
      inner ℝ (inclusion n 4 a) (inclusion n 4 (compactMixedOperatorDegreeFour n a)) := by
  have h1 : inner ℝ (inclusion n 5 (compactCovariantExterior n 4 a))
      (inclusion n 5 (compactSymmetricExterior n 4 a)) =
      inner ℝ (inclusion n 4 a) (inclusion n 4 (compactSymmetricContraction n 4 (compactCovariantExterior n 4 a))) :=
    (real_inner_comm _ _).trans (inner_symmetricExterior_four n a (compactCovariantExterior n 4 a))
  have h2 : inner ℝ (inclusion n 3 (compactCovariantAdjoint n 3 a))
      (inclusion n 3 (compactSymmetricContraction n 3 a)) =
      inner ℝ (inclusion n 4 a) (inclusion n 4 (compactCovariantExterior n 3 (compactSymmetricContraction n 3 a))) :=
    (real_inner_comm _ _).trans ((inner_covariantExterior_three n (compactSymmetricContraction n 3 a) a).symm.trans
      (real_inner_comm _ _))
  exact (congrArg₂ (· + ·) h1 h2).trans ((inner_add_right _ _ _).symm.trans
    (congrArg (inner ℝ (inclusion n 4 a)) ((inclusion n 4).map_add _ _).symm))

theorem mixedEnergyDegreeFour_eq_integral (n : ℕ) (a : Core n 4) :
    mixedEnergyDegreeFour n a =
      ∫ q, scalarPairing n 4 a.val (compactMixedOperatorDegreeFour n a).val q ∂orbitVolume :=
  (mixedEnergyDegreeFour_eq_inner_compactMixedOperatorDegreeFour n a).trans
    (inner_inclusion n 4 a (compactMixedOperatorDegreeFour n a))

theorem integral_compactCurrentDivergenceDegreeFour_eq (n : ℕ) (a : Core n 4) :
    (∫ q, compactCurrentDivergenceDegreeFour n a q ∂orbitVolume) = 2 * mixedEnergyDegreeFour n a :=
  (integral_const_mul 2 _).trans (congrArg (2 * ·) (mixedEnergyDegreeFour_eq_integral n a).symm)

theorem mixedEnergyDegreeFour_eq_zero_of_integral_current_zero (n : ℕ) (a : Core n 4)
    (h : (∫ q, compactCurrentDivergenceDegreeFour n a q ∂orbitVolume) = 0) :
    mixedEnergyDegreeFour n a = 0 := by
  have hz := (integral_compactCurrentDivergenceDegreeFour_eq n a).symm.trans h
  linarith

end TernaryPeriodPolynomials.Argument.Coercivity
