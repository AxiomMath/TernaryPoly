module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Mixed.OperatorThree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ScalarPairingThree
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Splitting

@[expose] public section



/-! Degree-3 specialization of the mixed-energy cross term (TWO surviving terms, mirroring the
original authors' degree-2 `mixedEnergy`/`compact_energy_expansion`
(`TernaryPeriodPolynomials/DifferentialForm/GeometricEnergy/Splitting.lean`) and its reduction to the compact mixed
operator and the descended current-divergence integral
(`TernaryPeriodPolynomials/DifferentialForm/GeometricEnergy/MixedIntegral.lean`), one level up: the "upper" cross
term uses `inner_symmetricExterior_three` (`ScalarPairingThree.lean`) and the "lower" one uses the
already-existing `inner_covariantExterior_two`
(`TernaryPeriodPolynomials/DifferentialForm/GeometricEnergy/Splitting.lean`). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The exact two mixed pairings at degree 3, mirroring `mixedEnergy` one level up. -/
def mixedEnergyThree (n : ℕ) (a : Core n 3) : ℝ :=
  inner ℝ (inclusion n 4 (compactCovariantExterior n 3 a)) (inclusion n 4 (compactSymmetricExterior n 3 a)) +
  inner ℝ (inclusion n 2 (compactCovariantAdjoint n 2 a)) (inclusion n 2 (compactSymmetricContraction n 2 a))

/-- Degree-3 energy expansion, mirroring `compact_energy_expansion` one level up. -/
theorem compact_energy_expansion_three (n : ℕ) (a : Core n 3) :
    ‖inclusion n 4 (compactDifferential (deckRepresentation n) isOpen_univ 3 a)‖ ^ 2 +
      ‖inclusion n 2 (compactAdjoint n 2 a)‖ ^ 2 =
    (‖inclusion n 4 (compactCovariantExterior n 3 a)‖ ^ 2 +
      ‖inclusion n 2 (compactCovariantAdjoint n 2 a)‖ ^ 2) +
    (‖inclusion n 4 (compactSymmetricExterior n 3 a)‖ ^ 2 +
      ‖inclusion n 2 (compactSymmetricContraction n 2 a)‖ ^ 2) + 2 * mixedEnergyThree n a :=
  (congrArg₂ (fun u v => ‖u‖ ^ 2 + ‖v‖ ^ 2) (inclusion_flat_sum n 3 a) (inclusion_adjoint_sum n 2 a)).trans
    (norm_pair_add_expansion _ _ _ _)

/-- `mixedEnergyThree` as a Hilbert pairing against the compact mixed operator, mirroring
`mixedEnergy_eq_inner_compactMixedOperator`. -/
theorem mixedEnergyThree_eq_inner_compactMixedOperatorThree (n : ℕ) (a : Core n 3) :
    mixedEnergyThree n a = inner ℝ (inclusion n 3 a) (inclusion n 3 (compactMixedOperatorThree n a)) := by
  have h1 : inner ℝ (inclusion n 4 (compactCovariantExterior n 3 a))
      (inclusion n 4 (compactSymmetricExterior n 3 a)) =
      inner ℝ (inclusion n 3 a) (inclusion n 3 (compactSymmetricContraction n 3 (compactCovariantExterior n 3 a))) :=
    (real_inner_comm _ _).trans (inner_symmetricExterior_three n a (compactCovariantExterior n 3 a))
  have h2 : inner ℝ (inclusion n 2 (compactCovariantAdjoint n 2 a))
      (inclusion n 2 (compactSymmetricContraction n 2 a)) =
      inner ℝ (inclusion n 3 a) (inclusion n 3 (compactCovariantExterior n 2 (compactSymmetricContraction n 2 a))) :=
    (real_inner_comm _ _).trans ((inner_covariantExterior_two n (compactSymmetricContraction n 2 a) a).symm.trans
      (real_inner_comm _ _))
  exact (congrArg₂ (· + ·) h1 h2).trans ((inner_add_right _ _ _).symm.trans
    (congrArg (inner ℝ (inclusion n 3 a)) ((inclusion n 3).map_add _ _).symm))

theorem mixedEnergyThree_eq_integral (n : ℕ) (a : Core n 3) :
    mixedEnergyThree n a = ∫ q, scalarPairing n 3 a.val (compactMixedOperatorThree n a).val q ∂orbitVolume :=
  (mixedEnergyThree_eq_inner_compactMixedOperatorThree n a).trans
    (inner_inclusion n 3 a (compactMixedOperatorThree n a))

theorem integral_compactCurrentDivergenceThree_eq (n : ℕ) (a : Core n 3) :
    (∫ q, compactCurrentDivergenceThree n a q ∂orbitVolume) = 2 * mixedEnergyThree n a :=
  (integral_const_mul 2 _).trans (congrArg (2 * ·) (mixedEnergyThree_eq_integral n a).symm)

theorem mixedEnergyThree_eq_zero_of_integral_current_zero (n : ℕ) (a : Core n 3)
    (h : (∫ q, compactCurrentDivergenceThree n a q ∂orbitVolume) = 0) : mixedEnergyThree n a = 0 := by
  have hz := (integral_compactCurrentDivergenceThree_eq n a).symm.trans h
  linarith

end TernaryPeriodPolynomials.Argument.Coercivity
