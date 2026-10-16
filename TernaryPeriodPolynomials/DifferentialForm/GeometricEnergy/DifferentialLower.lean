module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.MixedIntegral

@[expose] public section


/-! Genuine differential coercivity follows from the actual mixed-current integral vanishing. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormCoordinates PolynomialFormHilbert
open SmoothCoveringDeRham Set

/-- Exact lower bound, retaining the sole remaining integrated-divergence premise. -/
theorem algebraic_energy_le_flat_of_mixedEnergy_zero (n : ℕ) (a : Core n 2)
    (hm : mixedEnergy n a = 0) :
    ‖inclusion n 1 (compactSymmetricContraction n 1 a)‖ ^ 2 +
      ‖inclusion n 3 (compactSymmetricExterior n 2 a)‖ ^ 2 ≤
    ‖inclusion n 3 (compactDifferential (deckRepresentation n) isOpen_univ 2 a)‖ ^ 2 +
      ‖inclusion n 1 (compactAdjoint n 1 a)‖ ^ 2 := by
  have hArith (A B C D M E : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : M = 0)
      (hE : E = (C + D) + (B + A) + 2 * M) : A + B ≤ E := by linarith
  exact hArith _ _ _ _ _ _
    (sq_nonneg ‖inclusion n 3 (compactCovariantExterior n 2 a)‖)
    (sq_nonneg ‖inclusion n 1 (compactCovariantAdjoint n 1 a)‖) hm (compact_energy_expansion n a)

theorem norm_differential_energy_coercive_of_mixedEnergy_zero {n : ℕ} (hn : 0 < n)
    (hm : ∀ a : Core n 2, mixedEnergy n a = 0) :
    ∃ c > 0, ∀ a : Core n 2,
      c * ‖inclusion n 2 a‖ ^ 2 ≤
        ‖inclusion n 1 (compactAdjoint n 1 a)‖ ^ 2 +
          ‖inclusion n 3 (compactDifferential (deckRepresentation n) isOpen_univ 2 a)‖ ^ 2 := by
  exact Exists.imp (fun c h => ⟨h.1, fun a =>
    (h.2 a).trans ((algebraic_energy_le_flat_of_mixedEnergy_zero n a (hm a)).trans_eq (add_comm _ _))⟩)
    (norm_symmetric_energy_coercive hn)

end TernaryPoly.PolynomialFormGeometricEnergy
