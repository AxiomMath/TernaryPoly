module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Mixed.EnergyFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.QuotientCoerciveFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SixVanishing

@[expose] public section



/-! Degree-4/5 global mixed-energy cancellation and adjoint-differential coercivity, mirroring
`Cancellation.lean`'s degree-0 argument via `TernaryPoly.QuotientScalarDescent.integral_divergence_eq_zero`,
on the ADJOINT side (the top-degree clause bounds `‖D*a‖² + ‖Da‖²`, and `‖Da‖² = 0` identically by
`SixVanishing.lean`, since `Core n 6` is the trivial module). This is the final assembly file for
the degree-5 clause (`k = 4`) of Proposition C.1. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The degree-4/5 current-divergence integral vanishes, mirroring
`integral_compactCurrentDivergenceZero_zero`. -/
theorem integral_compactCurrentDivergenceFour_zero (n : ℕ) (a : Core n 5) :
    ∫ q, compactCurrentDivergenceFour n a q ∂orbitVolume = 0 :=
  TernaryPoly.QuotientScalarDescent.integral_divergence_eq_zero (energyCurrent n 5 a.val.val.val)
    (energyCurrent_compact_smooth n 5 a) (energyCurrent_isDeckVectorField n 5 a.val)
    (energyCurrent_compact_projected_support n 5 a) (compactCurrentDivergenceFour n a)
    (continuous_compactCurrentDivergenceFour n a) (compactCurrentDivergenceFour_coordinateProjection n a)

/-- The degree-4/5 mixed energy cross term vanishes, mirroring `mixedEnergyZero_zero`. -/
theorem mixedEnergyFour_zero (n : ℕ) (a : Core n 5) : mixedEnergyFour n a = 0 :=
  mixedEnergyFour_eq_zero_of_integral_current_zero n a (integral_compactCurrentDivergenceFour_zero n a)

/-- The degree-4/5 energy identity with the cross term eliminated, mirroring
`compact_energy_identity_zero`. -/
theorem compact_energy_identity_four (n : ℕ) (a : Core n 5) :
    ‖inclusion n 4 (compactAdjoint n 4 a)‖ ^ 2 =
      ‖inclusion n 4 (compactCovariantAdjoint n 4 a)‖ ^ 2 +
      ‖inclusion n 4 (compactSymmetricContraction n 4 a)‖ ^ 2 := by
  have h := compact_energy_expansion_four n a
  simpa only [mixedEnergyFour_zero n a, mul_zero, add_zero] using h

/-- Exact lower bound, retaining the sole remaining integrated-divergence premise, mirroring
`algebraic_energy_le_flat_of_mixedEnergyZero_zero`. -/
theorem algebraic_energy_le_flat_of_mixedEnergyFour_zero (n : ℕ) (a : Core n 5)
    (hm : mixedEnergyFour n a = 0) :
    ‖inclusion n 4 (compactSymmetricContraction n 4 a)‖ ^ 2 ≤
      ‖inclusion n 4 (compactAdjoint n 4 a)‖ ^ 2 := by
  have hArith (A C M E : ℝ) (hC : 0 ≤ C) (hM : M = 0) (hE : E = C + 2 * M + A) : A ≤ E := by linarith
  exact hArith _ _ _ _ (sq_nonneg ‖inclusion n 4 (compactCovariantAdjoint n 4 a)‖) hm
    (compact_energy_expansion_four n a)

/-- Mirroring `norm_differential_energy_coercive_of_mixedEnergy_zero`. -/
theorem norm_adjoint_energy_coercive_of_mixedEnergyFour_zero {n : ℕ} (hn : 0 < n)
    (hm : ∀ a : Core n 5, mixedEnergyFour n a = 0) :
    ∃ c > 0, ∀ a : Core n 5,
      c * ‖inclusion n 5 a‖ ^ 2 ≤ ‖inclusion n 4 (compactAdjoint n 4 a)‖ ^ 2 := by
  exact Exists.imp (fun c h => ⟨h.1, fun a =>
    (h.2 a).trans (algebraic_energy_le_flat_of_mixedEnergyFour_zero n a (hm a))⟩)
    (norm_symmetric_energy_coercive_four hn)

/-- Unconditional adjoint-side coercivity at degree 4/5, mirroring
`norm_differential_energy_coercive_zero`. -/
theorem norm_adjoint_energy_coercive_four {n : ℕ} (hn : 0 < n) :
    ∃ c > 0, ∀ a : Core n 5,
      c * ‖inclusion n 5 a‖ ^ 2 ≤ ‖inclusion n 4 (compactAdjoint n 4 a)‖ ^ 2 :=
  norm_adjoint_energy_coercive_of_mixedEnergyFour_zero hn (mixedEnergyFour_zero n)

/-- The degree-5 TARGET clause (`k = 4` of `coercivity_compact_support`): adjoint-differential coercivity for
compactly supported `Sym^n`-valued 5-forms on the neat cover with coefficients
`deckRepresentation n`. The `‖Da‖²` summand vanishes identically (`Core n 6` is trivial), so this
is `norm_adjoint_energy_coercive_four` with a dead summand reattached to match the literal
statement shape of `coercivity_compact_support`'s universally quantified clause at `k = 4`. -/
theorem norm_adjoint_differential_energy_coercive_four {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Core n 5,
      c * ‖inclusion n 5 a‖ ^ 2 ≤
        ‖inclusion n 4 (compactAdjoint n 4 a)‖ ^ 2 +
          ‖inclusion n 6 (compactDifferential (deckRepresentation n) isOpen_univ 5 a)‖ ^ 2 := by
  have hArith (L R Z : ℝ) (hZ : Z = 0) (hLR : L ≤ R) : L ≤ R + Z := by linarith
  exact Exists.imp (fun c h => ⟨h.1, fun a =>
    hArith _ _ _ (by rw [norm_compactDifferential_five_eq_zero n a]; norm_num) (h.2 a)⟩)
    (norm_adjoint_energy_coercive_four hn)

end TernaryPeriodPolynomials.Argument.Coercivity
