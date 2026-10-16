module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ScalarPairing

@[expose] public section



/-! Degree-0 specialization of the mixed-energy cross term and its reduction to the compact
mixed operator and the descended current-divergence integral, mirroring
`mixedEnergy`/`compact_energy_expansion`/`mixedEnergy_eq_inner_compactMixedOperator`/
`mixedEnergy_eq_integral`/`integral_compactCurrentDivergence_eq`/
`mixedEnergy_eq_zero_of_integral_current_zero`. At degree 0 there is only ONE cross term
(no adjoint-side term, since degree 0 has no `compactAdjoint n (-1)`), so each lemma collapses
to its first-summand analog. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The single mixed pairing at degree 0; mirrors `mixedEnergy`, dropping its second summand. -/
def mixedEnergyZero (n : ℕ) (a : Core n 0) : ℝ :=
  inner ℝ (inclusion n 1 (compactCovariantExterior n 0 a)) (inclusion n 1 (compactSymmetricExterior n 0 a))

/-- Degree-0 energy expansion, mirroring `compact_energy_expansion`. The RHS grouping matches
Mathlib's `norm_add_sq_real` directly, with no adjoint-side pair. -/
theorem compact_energy_expansion_zero (n : ℕ) (a : Core n 0) :
    ‖inclusion n 1 (compactDifferential (deckRepresentation n) isOpen_univ 0 a)‖ ^ 2 =
      ‖inclusion n 1 (compactCovariantExterior n 0 a)‖ ^ 2 + 2 * mixedEnergyZero n a +
      ‖inclusion n 1 (compactSymmetricExterior n 0 a)‖ ^ 2 :=
  (congrArg (fun u => ‖u‖ ^ 2) (inclusion_flat_sum n 0 a)).trans (norm_add_sq_real _ _)

/-- `mixedEnergyZero` as a Hilbert pairing against the compact mixed operator, mirroring
`mixedEnergy_eq_inner_compactMixedOperator`'s first (and here only) summand. -/
theorem mixedEnergyZero_eq_inner_compactMixedOperatorZero (n : ℕ) (a : Core n 0) :
    mixedEnergyZero n a = inner ℝ (inclusion n 0 a) (inclusion n 0 (compactMixedOperatorZero n a)) :=
  (real_inner_comm _ _).trans (inner_symmetricExterior_zero n a (compactCovariantExterior n 0 a))

/-- `mixedEnergyZero` as a descended scalar integral, mirroring `mixedEnergy_eq_integral`. -/
theorem mixedEnergyZero_eq_integral (n : ℕ) (a : Core n 0) :
    mixedEnergyZero n a = ∫ q, scalarPairing n 0 a.val (compactMixedOperatorZero n a).val q ∂orbitVolume :=
  (mixedEnergyZero_eq_inner_compactMixedOperatorZero n a).trans (inner_inclusion n 0 a (compactMixedOperatorZero n a))

/-- The current-divergence integral equals `2 * mixedEnergyZero`, mirroring
`integral_compactCurrentDivergence_eq`. -/
theorem integral_compactCurrentDivergenceZero_eq (n : ℕ) (a : Core n 0) :
    (∫ q, compactCurrentDivergenceZero n a q ∂orbitVolume) = 2 * mixedEnergyZero n a :=
  (integral_const_mul 2 _).trans (congrArg (2 * ·) (mixedEnergyZero_eq_integral n a).symm)

/-- A vanishing current-divergence integral forces `mixedEnergyZero` to vanish, mirroring
`mixedEnergy_eq_zero_of_integral_current_zero`. -/
theorem mixedEnergyZero_eq_zero_of_integral_current_zero (n : ℕ) (a : Core n 0)
    (h : (∫ q, compactCurrentDivergenceZero n a q ∂orbitVolume) = 0) : mixedEnergyZero n a = 0 := by
  have hz := (integral_compactCurrentDivergenceZero_eq n a).symm.trans h
  linarith

end TernaryPeriodPolynomials.Argument.Coercivity
