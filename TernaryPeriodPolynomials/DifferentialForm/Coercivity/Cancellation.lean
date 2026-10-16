module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Mixed.Energy
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.QuotientCoercive

@[expose] public section



/-! Degree-0 global mixed-energy cancellation and differential coercivity, mirroring
`PolynomialFormGeometricEnergyCancellation.lean`'s degree-2 argument via
`TernaryPoly.QuotientScalarDescent.integral_divergence_eq_zero` (the project's quotient
divergence theorem), specialized to the single degree-0 cross term with no adjoint-side
piece. This is the final assembly file for the degree-0 clause of Proposition C.1. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The degree-0 current-divergence integral vanishes, mirroring
`integral_compactCurrentDivergence_zero`. The call is fully qualified since this file's
namespace is not nested under the original library, unlike the project's own degree-2 original. -/
theorem integral_compactCurrentDivergenceZero_zero (n : ℕ) (a : Core n 0) :
    ∫ q, compactCurrentDivergenceZero n a q ∂orbitVolume = 0 :=
  TernaryPoly.QuotientScalarDescent.integral_divergence_eq_zero (energyCurrent n 0 a.val.val.val)
    (energyCurrent_compact_smooth n 0 a) (energyCurrent_isDeckVectorField n 0 a.val)
    (energyCurrent_compact_projected_support n 0 a) (compactCurrentDivergenceZero n a)
    (continuous_compactCurrentDivergenceZero n a) (compactCurrentDivergenceZero_coordinateProjection n a)

/-- The degree-0 mixed energy cross term vanishes, mirroring `mixedEnergy_zero`. -/
theorem mixedEnergyZero_zero (n : ℕ) (a : Core n 0) : mixedEnergyZero n a = 0 :=
  mixedEnergyZero_eq_zero_of_integral_current_zero n a (integral_compactCurrentDivergenceZero_zero n a)

/-- The degree-0 energy identity with the cross term eliminated, mirroring
`compact_energy_identity`. -/
theorem compact_energy_identity_zero (n : ℕ) (a : Core n 0) :
    ‖inclusion n 1 (compactDifferential (deckRepresentation n) isOpen_univ 0 a)‖ ^ 2 =
      ‖inclusion n 1 (compactCovariantExterior n 0 a)‖ ^ 2 +
      ‖inclusion n 1 (compactSymmetricExterior n 0 a)‖ ^ 2 := by
  have h := compact_energy_expansion_zero n a
  simpa only [mixedEnergyZero_zero n a, mul_zero, add_zero] using h

/-- Exact lower bound, retaining the sole remaining integrated-divergence premise, mirroring
`algebraic_energy_le_flat_of_mixedEnergy_zero`. -/
theorem algebraic_energy_le_flat_of_mixedEnergyZero_zero (n : ℕ) (a : Core n 0)
    (hm : mixedEnergyZero n a = 0) :
    ‖inclusion n 1 (compactSymmetricExterior n 0 a)‖ ^ 2 ≤
      ‖inclusion n 1 (compactDifferential (deckRepresentation n) isOpen_univ 0 a)‖ ^ 2 := by
  have hArith (A C M E : ℝ) (hC : 0 ≤ C) (hM : M = 0) (hE : E = C + 2 * M + A) : A ≤ E := by linarith
  exact hArith _ _ _ _ (sq_nonneg ‖inclusion n 1 (compactCovariantExterior n 0 a)‖) hm
    (compact_energy_expansion_zero n a)

/-- Mirroring `norm_differential_energy_coercive_of_mixedEnergy_zero`. -/
theorem norm_differential_energy_coercive_of_mixedEnergyZero_zero {n : ℕ} (hn : 0 < n)
    (hm : ∀ a : Core n 0, mixedEnergyZero n a = 0) :
    ∃ c > 0, ∀ a : Core n 0,
      c * ‖inclusion n 0 a‖ ^ 2 ≤
        ‖inclusion n 1 (compactDifferential (deckRepresentation n) isOpen_univ 0 a)‖ ^ 2 := by
  exact Exists.imp (fun c h => ⟨h.1, fun a =>
    (h.2 a).trans (algebraic_energy_le_flat_of_mixedEnergyZero_zero n a (hm a))⟩)
    (norm_symmetric_energy_coercive_zero hn)

/-- The degree-0 TARGET theorem: differential coercivity for compactly supported `Sym^n`-valued
0-forms on the neat cover with coefficients `deckRepresentation n`, mirroring
`norm_differential_energy_coercive`. Degree 0 has no adjoint term, so `‖D a‖² ` alone is bounded
below by `c‖a‖²`. -/
theorem norm_differential_energy_coercive_zero {n : ℕ} (hn : 0 < n) :
    ∃ c > 0, ∀ a : Core n 0,
      c * ‖inclusion n 0 a‖ ^ 2 ≤
        ‖inclusion n 1 (compactDifferential (deckRepresentation n) isOpen_univ 0 a)‖ ^ 2 :=
  norm_differential_energy_coercive_of_mixedEnergyZero_zero hn (mixedEnergyZero_zero n)

end TernaryPeriodPolynomials.Argument.Coercivity
