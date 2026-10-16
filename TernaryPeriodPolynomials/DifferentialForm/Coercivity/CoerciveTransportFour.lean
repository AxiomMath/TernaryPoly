module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ContractionBound

@[expose] public section



/-! Transport of the degree-4 basepoint coercivity bound `symmetric_energy_basepoint_coercive_four`
to every point of the positive cone, mirroring `CoerciveTransport.lean`'s
`symmetric_energy_coercive_zero` via the project's generic real-frame transport machinery,
substituting `symmetricContraction_real` for `symmetricExterior_real` (the top-degree bound
constrains `symmetricContraction n 4`, not `symmetricExterior n 0`). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive

/-- Everywhere degree-4 coercivity for `symmetricContraction n 4`, mirroring
`symmetric_energy_coercive_zero`'s transport argument. -/
theorem symmetric_energy_coercive_four {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ w : FormValue n 5,
      c * formPairing n 5 x w w ≤
        formPairing n 4 x (symmetricContraction n 4 x w) (symmetricContraction n 4 x w) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine ⟨(n : ℝ) * (n + 9) / 24, by nlinarith, fun x hx w => ?_⟩
  obtain ⟨g, hg, he⟩ := exists_normalized_real_frame x hx
  rw [← he]
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let b := realFormPullback n 5 g y w
  have hb := realFormPullback_spec n 5 g y w
  have hE := symmetricContraction_real n 4 g hg y hy w b hb
  rw [formPairing_real n 5 g hg y hy w w b b hb hb,
    formPairing_real n 4 g hg y hy _ _ _ _ hE hE]
  exact symmetric_energy_basepoint_coercive_four n b

end TernaryPeriodPolynomials.Argument.Coercivity
