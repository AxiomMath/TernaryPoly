module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CasimirBound

@[expose] public section



/-! Transport of the degree-0 basepoint coercivity bound `symmetric_energy_basepoint_coercive_zero`
to every point of the positive cone, mirroring `symmetric_energy_coercive`'s proof via the
project's generic real-frame transport machinery. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SmoothCoveringDeRham
open ContinuousAlternatingMap

/-- Everywhere degree-0 coercivity, mirroring `symmetric_energy_coercive`'s basepoint-to-everywhere
transport argument via `exists_normalized_real_frame` and the real-frame pullback compatibility
lemmas `realFormPullback_spec`/`symmetricExterior_real`/`formPairing_real`. -/
theorem symmetric_energy_coercive_zero {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ a : FormValue n 0,
      c * formPairing n 0 x a a ≤
        formPairing n 1 x (symmetricExterior n 0 x a) (symmetricExterior n 0 x a) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine ⟨(n : ℝ) * (n + 9) / 24, by nlinarith, fun x hx a => ?_⟩
  obtain ⟨g, hg, he⟩ := exists_normalized_real_frame x hx
  rw [← he]
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let b := realFormPullback n 0 g y a
  have hb := realFormPullback_spec n 0 g y a
  have hE := symmetricExterior_real n 0 g hg y hy a b hb
  rw [formPairing_real n 0 g hg y hy a a b b hb hb,
    formPairing_real n 1 g hg y hy _ _ _ _ hE hE]
  exact symmetric_energy_basepoint_coercive_zero b

end TernaryPeriodPolynomials.Argument.Coercivity
