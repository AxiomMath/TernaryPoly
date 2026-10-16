module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseAdjoint

@[expose] public section


/-! Actual symmetric-connection algebraic energy at the metric basepoint. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open SL3PolynomialCoercivity PolynomialCoefficientMetric PolynomialFormMetric
open SymmetricSpaceCharts SymmetricSpaceCovering

theorem symmetricHodgeTwo_basepoint_energy (n : ℕ) (a : FormValue n 2) :
    formPairing n 2 (coordinateChart basepoint) (symmetricHodgeTwo n (coordinateChart basepoint) a) a =
      formPairing n 1 (coordinateChart basepoint) (symmetricContraction n 1 (coordinateChart basepoint) a)
        (symmetricContraction n 1 (coordinateChart basepoint) a) +
      formPairing n 3 (coordinateChart basepoint) (symmetricExterior n 2 (coordinateChart basepoint) a)
        (symmetricExterior n 2 (coordinateChart basepoint) a) := by
  rw [symmetricHodgeTwo, formPairing_add_left, symmetricExterior_one_basepoint_adjoint]
  congr 1
  have hx : coordinateChart basepoint ∈ positiveCoordinates := extract_mem basepoint
  rw [formPairing_symm n 2 (coordinateChart basepoint) hx, ← symmetricExterior_two_basepoint_adjoint]

theorem symmetricHodgeTwo_basepoint_nonneg (n : ℕ) (a : FormValue n 2) :
    0 ≤ formPairing n 2 (coordinateChart basepoint) (symmetricHodgeTwo n (coordinateChart basepoint) a) a := by
  rw [symmetricHodgeTwo_basepoint_energy]
  exact add_nonneg (formPairing_nonneg n 1 _ (extract_mem basepoint) _)
    (formPairing_nonneg n 3 _ (extract_mem basepoint) _)

theorem symmetric_energy_basepoint_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : FormValue n 2,
      c * formPairing n 2 (coordinateChart basepoint) a a ≤
        formPairing n 1 (coordinateChart basepoint) (symmetricContraction n 1 (coordinateChart basepoint) a)
          (symmetricContraction n 1 (coordinateChart basepoint) a) +
        formPairing n 3 (coordinateChart basepoint) (symmetricExterior n 2 (coordinateChart basepoint) a)
          (symmetricExterior n 2 (coordinateChart basepoint) a) := by
  obtain ⟨c,hc,h⟩ := symmetricHodgeTwo_basepoint_coercive hn
  exact ⟨c,hc,fun a => by rw [← symmetricHodgeTwo_basepoint_energy]; exact h a⟩

end TernaryPoly.PolynomialFormGeometricEnergy
