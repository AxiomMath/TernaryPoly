module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.Integration
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalAdjoint

@[expose] public section


/-! Actual vanishing of the integrated density-weighted divergence of a compact coordinate field. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open Set MeasureTheory
open scoped ContDiff
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem integral_weighted_divergence_eq_zero {U : Set E} (hU : IsOpen U)
    (ρ : E → ℝ) (hρ : ContDiffOn ℝ ∞ ρ U) (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (V : I → E → ℝ) (v : I → E) (hV : ∀ i, ContDiff ℝ ∞ (V i))
    (hcV : ∀ i, HasCompactSupport (V i)) (hsV : ∀ i, tsupport (V i) ⊆ U) :
    ∫ x, ρ x * ((ρ x)⁻¹ * ∑ i, fderiv ℝ (fun y => ρ y * V i y) x (v i)) ∂μ = 0 := by
  let g (i : I) (x : E) := ρ x * V i x
  have hgs (i : I) : tsupport (g i) ⊆ U := tsupport_mul_subset_right.trans (hsV i)
  have hg (i : I) : ContDiff ℝ ∞ (g i) :=
    contDiff_of_tsupport_subset hU (hρ.mul (hV i).contDiffOn) (hgs i)
  have hgc (i : I) : HasCompactSupport (g i) := (hcV i).mul_left
  have hi (i : I) : Integrable (fun x => fderiv ℝ (g i) x (v i)) μ :=
    (((hg i).of_le (by simp) : ContDiff ℝ 1 (g i)).continuous_fderiv one_ne_zero |>.clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hgc i).fderiv_apply ℝ (v i))
  have he (x : E) : ρ x * ((ρ x)⁻¹ * ∑ i, fderiv ℝ (g i) x (v i)) =
      ∑ i, fderiv ℝ (g i) x (v i) := by
    by_cases hx : x ∈ U
    · rw [← mul_assoc, mul_inv_cancel₀ (hρ0 x hx), one_mul]
    · have hz : ∑ i, fderiv ℝ (g i) x (v i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hgs i h))]
        rfl
      rw [hz, mul_zero, mul_zero]
  calc
    _ = ∫ x, ∑ i, fderiv ℝ (g i) x (v i) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall he)
    _ = ∑ i, ∫ x, fderiv ℝ (g i) x (v i) ∂μ := integral_finsetSum _ (fun i _ => hi i)
    _ = 0 := Finset.sum_eq_zero (fun i _ => integral_fderiv_eq_zero
      ((hg i).of_le (by simp)) (hgc i) (v i))

end TernaryPoly.CompactCoordinateIntegration
