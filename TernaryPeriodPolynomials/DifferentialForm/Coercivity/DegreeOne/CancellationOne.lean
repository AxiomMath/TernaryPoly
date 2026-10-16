module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.MixedEnergyOne
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.QuotientCoerciveOne
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentSupport
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDeck
public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.GlobalDivergence

@[expose] public section



/-! Degree-1 global mixed-energy cancellation and differential coercivity: the TARGET theorem
`norm_differential_energy_coercive_one`, mirroring the original authors' own genuine two-term
degree-2 argument (`TernaryPoly.PolynomialFormGeometricEnergy.compact_energy_identity`/
`algebraic_energy_le_flat_of_mixedEnergy_zero`/`norm_differential_energy_coercive_of_mixedEnergy_zero`/
`norm_differential_energy_coercive`, `TernaryPeriodPolynomials/DifferentialForm/GeometricEnergy/Cancellation.lean` and
`TernaryPeriodPolynomials/DifferentialForm/GeometricEnergy/DifferentialLower.lean`, both read-only reference) one
level down via `TernaryPoly.QuotientScalarDescent.integral_divergence_eq_zero` (mirroring
`CancellationThree.lean`'s/`Cancellation.lean`'s identical call pattern), using the new `geomMixedEnergyOne` (`MixedEnergyOne.lean`) in place of the two-term `mixedEnergy`, and the new `norm_symmetric_energy_coercive_one` (`QuotientCoerciveOne.lean`) in place of
`norm_symmetric_energy_coercive`. This completes pipeline steps 4-5 and closes Proposition C.1's
exterior degree 1 clause. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.CoercivityOne

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The degree-1 current-divergence integral vanishes, mirroring
`integral_compactCurrentDivergence_zero`/`integral_compactCurrentDivergenceThree_zero`. -/
theorem integral_compactCurrentDivergenceOne_zero (n : ℕ) (a : Core n 1) :
    ∫ q, compactCurrentDivergenceOne n a q ∂orbitVolume = 0 :=
  TernaryPoly.QuotientScalarDescent.integral_divergence_eq_zero (energyCurrent n 1 a.val.val.val)
    (energyCurrent_compact_smooth n 1 a) (energyCurrent_isDeckVectorField n 1 a.val)
    (energyCurrent_compact_projected_support n 1 a) (compactCurrentDivergenceOne n a)
    (continuous_compactCurrentDivergenceOne n a) (compactCurrentDivergenceOne_coordinateProjection n a)

/-- The degree-1 mixed energy cross terms vanish, mirroring `mixedEnergy_zero`/`mixedEnergyThree_zero`. -/
theorem geomMixedEnergyOne_zero (n : ℕ) (a : Core n 1) : geomMixedEnergyOne n a = 0 :=
  geomMixedEnergyOne_eq_zero_of_integral_current_zero n a (integral_compactCurrentDivergenceOne_zero n a)

/-- The degree-1 energy identity with the cross terms eliminated, mirroring
`compact_energy_identity`/`compact_energy_identity_three`. -/
theorem compact_energy_identity_one (n : ℕ) (a : Core n 1) :
    ‖inclusion n 2 (compactDifferential (deckRepresentation n) isOpen_univ 1 a)‖ ^ 2 +
      ‖inclusion n 0 (compactAdjoint n 0 a)‖ ^ 2 =
    (‖inclusion n 2 (compactCovariantExterior n 1 a)‖ ^ 2 +
      ‖inclusion n 0 (compactCovariantAdjoint n 0 a)‖ ^ 2) +
    (‖inclusion n 2 (compactSymmetricExterior n 1 a)‖ ^ 2 +
      ‖inclusion n 0 (compactSymmetricContraction n 0 a)‖ ^ 2) := by
  have h := compact_energy_expansion_one n a
  simpa only [geomMixedEnergyOne_zero n a, mul_zero, add_zero] using h

/-- Exact lower bound, retaining the sole remaining integrated-divergence premise, mirroring
`algebraic_energy_le_flat_of_mixedEnergy_zero`. -/
theorem algebraic_energy_le_flat_of_geomMixedEnergyOne_zero (n : ℕ) (a : Core n 1)
    (hm : geomMixedEnergyOne n a = 0) :
    ‖inclusion n 0 (compactSymmetricContraction n 0 a)‖ ^ 2 +
      ‖inclusion n 2 (compactSymmetricExterior n 1 a)‖ ^ 2 ≤
    ‖inclusion n 2 (compactDifferential (deckRepresentation n) isOpen_univ 1 a)‖ ^ 2 +
      ‖inclusion n 0 (compactAdjoint n 0 a)‖ ^ 2 := by
  have hArith (A B C D M E : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : M = 0)
      (hE : E = (C + D) + (B + A) + 2 * M) : A + B ≤ E := by linarith
  exact hArith _ _ _ _ _ _
    (sq_nonneg ‖inclusion n 2 (compactCovariantExterior n 1 a)‖)
    (sq_nonneg ‖inclusion n 0 (compactCovariantAdjoint n 0 a)‖) hm (compact_energy_expansion_one n a)

/-- Mirroring `norm_differential_energy_coercive_of_mixedEnergy_zero`. -/
theorem norm_differential_energy_coercive_of_geomMixedEnergyOne_zero {n : ℕ} (hn : 0 < n)
    (hm : ∀ a : Core n 1, geomMixedEnergyOne n a = 0) :
    ∃ c > 0, ∀ a : Core n 1,
      c * ‖inclusion n 1 a‖ ^ 2 ≤
        ‖inclusion n 0 (compactAdjoint n 0 a)‖ ^ 2 +
          ‖inclusion n 2 (compactDifferential (deckRepresentation n) isOpen_univ 1 a)‖ ^ 2 := by
  exact Exists.imp (fun c h => ⟨h.1, fun a =>
    (h.2 a).trans ((algebraic_energy_le_flat_of_geomMixedEnergyOne_zero n a (hm a)).trans_eq (add_comm _ _))⟩)
    (norm_symmetric_energy_coercive_one hn)

/-- The degree-1 TARGET theorem: differential coercivity for compactly supported `Sym^n`-valued
1-forms on the neat cover with coefficients `deckRepresentation n`, mirroring
`norm_differential_energy_coercive`. This is exactly the shape of
`norm_differential_energy_coercive_one`. -/
theorem norm_differential_energy_coercive_one {n : ℕ} (hn : 0 < n) :
    ∃ c > 0, ∀ a : Core n 1,
      c * ‖inclusion n 1 a‖ ^ 2 ≤
        ‖inclusion n 0 (compactAdjoint n 0 a)‖ ^ 2 +
          ‖inclusion n 2 (compactDifferential (deckRepresentation n) isOpen_univ 1 a)‖ ^ 2 :=
  norm_differential_energy_coercive_of_geomMixedEnergyOne_zero hn (geomMixedEnergyOne_zero n)

end TernaryPeriodPolynomials.Argument.CoercivityOne
