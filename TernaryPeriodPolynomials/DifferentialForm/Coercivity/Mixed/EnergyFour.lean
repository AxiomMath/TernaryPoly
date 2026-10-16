module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Mixed.OperatorFour

@[expose] public section



/-! Degree-4/5 specialization of the mixed-energy cross term and its reduction to the compact
mixed operator and the descended current-divergence integral, mirroring `MixedEnergy.lean`'s
degree-0 `mixedEnergyZero` family, on the ADJOINT side (`compactAdjoint n 4 = compactCovariantAdjoint
n 4 + compactSymmetricContraction n 4`, via `inclusion_adjoint_sum`) rather than the degree-0 FLAT
side. The reduction to the compact mixed
operator uses `inner_covariantExterior_four` (`CovariantAdjointFour.lean`) bracketed by an extra
`real_inner_comm` on each side, since `inner_covariantExterior_four`'s own statement pairs at the
output level (`compactCovariantExterior n 4 _`, degree 5), unlike degree 0's
`inner_symmetricExterior_zero`, which already pairs in the needed order directly. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The single mixed pairing at degree 4 (adjoint side), mirroring `mixedEnergyZero`. -/
def mixedEnergyFour (n : ℕ) (a : Core n 5) : ℝ :=
  inner ℝ (inclusion n 4 (compactCovariantAdjoint n 4 a)) (inclusion n 4 (compactSymmetricContraction n 4 a))

/-- Degree-4/5 energy expansion on the adjoint side, mirroring `compact_energy_expansion_zero`. -/
theorem compact_energy_expansion_four (n : ℕ) (a : Core n 5) :
    ‖inclusion n 4 (compactAdjoint n 4 a)‖ ^ 2 =
      ‖inclusion n 4 (compactCovariantAdjoint n 4 a)‖ ^ 2 + 2 * mixedEnergyFour n a +
      ‖inclusion n 4 (compactSymmetricContraction n 4 a)‖ ^ 2 :=
  (congrArg (fun u => ‖u‖ ^ 2) (inclusion_adjoint_sum n 4 a)).trans (norm_add_sq_real _ _)

/-- `mixedEnergyFour` as a Hilbert pairing against the compact mixed operator, mirroring
`mixedEnergyZero_eq_inner_compactMixedOperatorZero`. -/
theorem mixedEnergyFour_eq_inner_compactMixedOperatorFour (n : ℕ) (a : Core n 5) :
    mixedEnergyFour n a = inner ℝ (inclusion n 5 a) (inclusion n 5 (compactMixedOperatorFour n a)) := by
  calc mixedEnergyFour n a
      = inner ℝ (inclusion n 4 (compactSymmetricContraction n 4 a))
          (inclusion n 4 (compactCovariantAdjoint n 4 a)) := real_inner_comm _ _
    _ = inner ℝ (inclusion n 5 (compactCovariantExterior n 4 (compactSymmetricContraction n 4 a)))
          (inclusion n 5 a) := (inner_covariantExterior_four n (compactSymmetricContraction n 4 a) a).symm
    _ = inner ℝ (inclusion n 5 a) (inclusion n 5 (compactMixedOperatorFour n a)) := real_inner_comm _ _

/-- `mixedEnergyFour` as a descended scalar integral, mirroring `mixedEnergyZero_eq_integral`. -/
theorem mixedEnergyFour_eq_integral (n : ℕ) (a : Core n 5) :
    mixedEnergyFour n a = ∫ q, scalarPairing n 5 a.val (compactMixedOperatorFour n a).val q ∂orbitVolume :=
  (mixedEnergyFour_eq_inner_compactMixedOperatorFour n a).trans
    (inner_inclusion n 5 a (compactMixedOperatorFour n a))

/-- The current-divergence integral equals `2 * mixedEnergyFour`, mirroring
`integral_compactCurrentDivergenceZero_eq`. -/
theorem integral_compactCurrentDivergenceFour_eq (n : ℕ) (a : Core n 5) :
    (∫ q, compactCurrentDivergenceFour n a q ∂orbitVolume) = 2 * mixedEnergyFour n a :=
  (integral_const_mul 2 _).trans (congrArg (2 * ·) (mixedEnergyFour_eq_integral n a).symm)

/-- A vanishing current-divergence integral forces `mixedEnergyFour` to vanish, mirroring
`mixedEnergyZero_eq_zero_of_integral_current_zero`. -/
theorem mixedEnergyFour_eq_zero_of_integral_current_zero (n : ℕ) (a : Core n 5)
    (h : (∫ q, compactCurrentDivergenceFour n a q ∂orbitVolume) = 0) : mixedEnergyFour n a = 0 := by
  have hz := (integral_compactCurrentDivergenceFour_eq n a).symm.trans h
  linarith

end TernaryPeriodPolynomials.Argument.Coercivity
