module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence.Density

@[expose] public section


/-! The literal density-weighted divergence obeys the genuine scalar product rule. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open PolynomialFormMetric SymmetricSpaceCharts
open scoped Matrix.Norms.Elementwise

theorem fderiv_scalar_vector_apply (ψ : Coordinates → ℝ) (V : Coordinates → Coordinates)
    (x u : Coordinates) (hψ : DifferentiableAt ℝ ψ x) (hV : DifferentiableAt ℝ V x) (i : Fin 5) :
    fderiv ℝ (fun y => ψ y • V y) x u i =
      ψ x * fderiv ℝ V x u i + fderiv ℝ ψ x u * V x i := by
  have h := fderiv_fun_smul (𝕜 := ℝ) (c := ψ) (f := V) (x := x) hψ hV
  have he := congrArg (fun L => L u i) h
  simpa only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] using he

theorem coordinateLinear_sum (L : Coordinates →L[ℝ] ℝ) (v : Coordinates) :
    L v = ∑ i : Fin 5, v i * L (Pi.single i 1) := by
  have h := congrArg L (pi_eq_sum_univ' v)
  simpa only [map_sum, map_smul, smul_eq_mul] using h

/-- Actual density-weighted divergence, with only pointwise differentiability assumptions. -/
theorem weightedDivergence_smul (ψ : Coordinates → ℝ) (V : Coordinates → Coordinates)
    (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (hψ : DifferentiableAt ℝ ψ x) (hV : DifferentiableAt ℝ V x) :
    weightedDivergence (fun y => ψ y • V y) x =
      ψ x * weightedDivergence V x + fderiv ℝ ψ x (V x) := by
  have hprod : DifferentiableAt ℝ (fun y => ψ y • V y) x := hψ.smul hV
  rw [weightedDivergence_expansion _ x hx hprod, weightedDivergence_expansion V x hx hV,
    coordinateLinear_sum (fderiv ℝ ψ x) (V x)]
  simp only [fderiv_scalar_vector_apply ψ V x _ hψ hV, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end TernaryPoly.PolynomialFormConnection
