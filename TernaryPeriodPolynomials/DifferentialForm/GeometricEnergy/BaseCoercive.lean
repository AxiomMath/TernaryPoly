module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Hodge

@[expose] public section


/-! Positive-degree coercivity of the actual algebraic connection term at the metric basepoint. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open SL3PolynomialCoercivity PolynomialCoefficientMetric PolynomialFormMetric
open SymmetricSpaceCovering SymmetricSpaceCharts

/-- The geometrically forced quarter factor retains a strictly positive coercivity constant. -/
theorem symmetricHodgeTwo_basepoint_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : FormValue n 2,
      c * formPairing n 2 (coordinateChart basepoint) a a ≤
        formPairing n 2 (coordinateChart basepoint) (symmetricHodgeTwo n (coordinateChart basepoint) a) a := by
  obtain ⟨c, hc, h⟩ := homogeneousHodgeTwo_basepoint_coercive hn
  refine ⟨c / 4, div_pos hc (by norm_num), fun a => ?_⟩
  rw [formPairing_basepoint_two, formPairing_basepoint_two,
    symmetricHodgeTwo_basepoint_coordinates, twoPairing_smul_left]
  have hh := h a
  rw [formPairing_basepoint_two] at hh
  change c * twoPairing (baseTwoCoordinates a) (baseTwoCoordinates a) ≤
    twoPairing (algebraicHodgeTwo (baseTwoCoordinates a)) (baseTwoCoordinates a) at hh
  nlinarith

end TernaryPoly.PolynomialFormGeometricEnergy
