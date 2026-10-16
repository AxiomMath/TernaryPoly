module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.SupportedNorm
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section


/-! Coordinate L2 convergence controls the actual Hilbert norm on a fixed compact chart support. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped Topology

theorem chart_supported_inclusion_tendsto_zero {ι : Type*} {l : Filter ι}
    (n k : ℕ) (S : Space) (K : Set Coordinates) (hcK : IsCompact K) (hsK : K ⊆ (quotientChart S).target)
    (w : ι → Core n k) (hw : ∀ j, quotientSupport (w j).val ⊆ (quotientChart S).symm '' K)
    (ht : ∀ i : Index n k, Tendsto (fun j => ∫ x,
      ‖components n k (globalChartRepresentative (deckRepresentation n) S k (w j).val).val i x‖^2) l (𝓝 0)) :
    Tendsto (fun j => inclusion n k (w j)) l (𝓝 0) := by
  have HB := exists_chart_supported_norm_bound n k S K hcK hsK
  let B : ℝ := HB.choose
  have hs : Tendsto (fun j => B * ∑ i, ∫ x,
      ‖components n k (globalChartRepresentative (deckRepresentation n) S k (w j).val).val i x‖^2) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero, mul_zero] using
      (tendsto_finsetSum Finset.univ (fun i _ => ht i)).const_mul B
  have hn : Tendsto (fun j => ‖inclusion n k (w j)‖^2) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun j => sq_nonneg _))
      (Eventually.of_forall (fun j => HB.choose_spec.2 (w j) (hw j))) hs
  have hr := (Real.continuous_sqrt.tendsto 0).comp hn
  have hnorm : Tendsto (fun j => ‖inclusion n k (w j)‖) l (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hnorm

end TernaryPoly.PolynomialFormCoordinates
