module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.WeightedConvergence
public import TernaryPeriodPolynomials.DifferentialForm.Chart.DifferenceNorm
public import TernaryPeriodPolynomials.DifferentialForm.Chart.NormFormulas
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section


/-! Genuine Hilbert convergence of actual chart mollifiers to the double cutoff. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)

def doubleChartCutoff (w : EquivariantForm (deckRepresentation n) univ k) : Core n k :=
  chartCutoff n k S (η*χ) (hη.mul hχ) hcη.mul_right (tsupport_mul_subset_left.trans hsη) w

include hcχ in
theorem chartMollifier_inclusion_tendsto (w : EquivariantForm (deckRepresentation n) univ k) :
    Tendsto (fun j : ℕ => inclusion n k
      (chartMollifier n k S χ η ((j:ℝ)+1) (by positivity) hχ hsχ hη hcη hsη w)) atTop
      (nhds (inclusion n k (doubleChartCutoff n k S χ η hχ hη hcη hsη w))) := by
  let b := doubleChartCutoff n k S χ η hχ hη hcη hsη w
  let a (j : ℕ) := chartMollifier n k S χ η ((j:ℝ)+1) (by positivity) hχ hsχ hη hcη hsη w
  have hb := quotientSupport_chartCutoff n k S (η*χ) (hη.mul hχ) hcη.mul_right
    (tsupport_mul_subset_left.trans hsη) w
  have hgb : (globalChartRepresentative (deckRepresentation n) S k b.val).val =
      fun x => η x • cutoffChartRaw n k S χ w x := by
    have h := globalChartRepresentative_chartCutoff n k S (η*χ) (hη.mul hχ) hcη.mul_right
      (tsupport_mul_subset_left.trans hsη) w
    refine h.trans (funext (fun x => ?_))
    exact mul_smul (η x) (χ x) ((globalChartRepresentative (deckRepresentation n) S k w).val x)
  have he (j : ℕ) : ‖inclusion n k (a j) - inclusion n k b‖^2 =
      ∫ x, weightedSquare n k
        (fun y => mollifiedChartRaw n k S χ η ((j:ℝ)+1) w y - η y • cutoffChartRaw n k S χ w y) x :=
    norm_inclusion_sub_square_chart n k S (a j) b
      (quotientSupport_chartMollifier_source n k S χ η ((j:ℝ)+1) (by positivity) hχ hsχ hη hcη hsη w) hb
      _ _ (globalChartRepresentative_chartMollifier n k S χ η ((j:ℝ)+1) (by positivity) hχ hsχ hη hcη hsη w) hgb
  have hscale : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun j : ℕ => ‖inclusion n k (a j) - inclusion n k b‖^2) atTop (nhds 0) := by
    simp_rw [he]
    exact (mollifiedChartRaw_weighted_tendsto n k S χ η hχ hcχ hsχ hη hcη hsη w).comp hscale
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht' := (Real.continuous_sqrt.tendsto 0).comp ht
  change Tendsto (fun j : ℕ => Real.sqrt (‖inclusion n k (a j) - inclusion n k b‖^2))
    atTop (nhds (Real.sqrt 0)) at ht'
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht'

end TernaryPoly.PolynomialFormCoordinates
