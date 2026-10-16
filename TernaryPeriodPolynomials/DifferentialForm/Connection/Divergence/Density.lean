module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence

@[expose] public section


/-! Exact expansion of the literal density-weighted divergence. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SymmetricSpaceCharts SymmetricSpaceRiemannian
open scoped Matrix.Norms.Elementwise

theorem hasDerivAt_densityProduct_line (V : Coordinates → Coordinates) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (hV : DifferentiableAt ℝ V x) (u : Coordinates) (i : Fin 5) :
    HasDerivAt (fun t : ℝ => coordinateDensity (x + t • u) * V (x + t • u) i)
      (coordinateDensity x * ((tangentConnectionMatrix x u).trace * V x i + fderiv ℝ V x u i)) 0 := by
  have h := (hasDerivAt_coordinateDensity_connection x hx u).mul
    (hasDerivAt_pi.mp (hasDerivAt_tangentSection_line V x u hV) i)
  convert! h using 1
  simp only [zero_smul, add_zero]
  ring

theorem fderiv_densityProduct (V : Coordinates → Coordinates) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (hV : DifferentiableAt ℝ V x) (u : Coordinates) (i : Fin 5) :
    fderiv ℝ (fun y => coordinateDensity y * V y i) x u =
      coordinateDensity x * ((tangentConnectionMatrix x u).trace * V x i + fderiv ℝ V x u i) := by
  have hd := (((contDiffOn_coordinateDensity x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)).mul (differentiableAt_pi.mp hV i)
  have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_coordinateLine x u)
    (by simp only [zero_smul, add_zero])
  exact h.unique (hasDerivAt_densityProduct_line V x hx hV u i)

/-- The coordinate weighted divergence has exactly the metric-connection trace correction. -/
theorem weightedDivergence_expansion (V : Coordinates → Coordinates) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (hV : DifferentiableAt ℝ V x) :
    weightedDivergence V x = ∑ i : Fin 5,
      ((tangentConnectionMatrix x (Pi.single i 1)).trace * V x i + fderiv ℝ V x (Pi.single i 1) i) := by
  unfold weightedDivergence
  simp only [fderiv_densityProduct V x hx hV, ← Finset.mul_sum]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (coordinateDensity_pos x hx)), one_mul]

end TernaryPoly.PolynomialFormConnection
