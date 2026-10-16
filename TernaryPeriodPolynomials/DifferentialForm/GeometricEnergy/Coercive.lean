module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Adjoint

@[expose] public section


/-! Uniform positive-degree algebraic coercivity for the actual geometric symmetric connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

/-- The basepoint constant works everywhere, by proved real-frame transport. -/
theorem symmetric_energy_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ a : FormValue n 2,
      c * formPairing n 2 x a a ≤
        formPairing n 1 x (symmetricContraction n 1 x a) (symmetricContraction n 1 x a) +
        formPairing n 3 x (symmetricExterior n 2 x a) (symmetricExterior n 2 x a) := by
  obtain ⟨c,hc,h⟩ := symmetric_energy_basepoint_coercive hn
  refine ⟨c,hc,fun x hx a => ?_⟩
  obtain ⟨g,hg,he⟩ := exists_normalized_real_frame x hx
  rw [← he]
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let b := realFormPullback n 2 g y a
  have hb := realFormPullback_spec n 2 g y a
  have hC := symmetricContraction_real n 1 g hg y hy a b hb
  have hE := symmetricExterior_real n 2 g hg y hy a b hb
  rw [formPairing_real n 2 g hg y hy a a b b hb hb,
    formPairing_real n 1 g hg y hy _ _ _ _ hC hC,
    formPairing_real n 3 g hg y hy _ _ _ _ hE hE]
  exact h b

/-- The actual Hodge term has a point-independent positive lower bound for every n>0. -/
theorem symmetricHodgeTwo_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ a : FormValue n 2,
      c * formPairing n 2 x a a ≤ formPairing n 2 x (symmetricHodgeTwo n x a) a := by
  obtain ⟨c,hc,h⟩ := symmetric_energy_coercive hn
  refine ⟨c,hc,fun x hx a => ?_⟩
  rw [symmetricHodgeTwo_energy n x hx]
  exact h x hx a

end TernaryPoly.PolynomialFormGeometricEnergy
