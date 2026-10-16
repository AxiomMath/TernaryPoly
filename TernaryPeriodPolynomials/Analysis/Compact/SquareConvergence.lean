module

public import TernaryPeriodPolynomials.Analysis.Compact.SquareSum
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Bound
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Algebra.Order.Group.DenselyOrdered

@[expose] public section


/-! Sums and compact scalar multiplication preserve genuine square-integral convergence. -/
namespace TernaryPoly.CompactSquareIntegral
open MeasureTheory Filter
variable {E ι : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {l : Filter ι}

theorem integral_add_square_tendsto_zero (f g : ι → E → ℝ)
    (hf : ∀ᶠ c in l, Continuous (f c)) (hg : ∀ᶠ c in l, Continuous (g c))
    (hcf : ∀ᶠ c in l, HasCompactSupport (f c)) (hcg : ∀ᶠ c in l, HasCompactSupport (g c))
    (htf : Tendsto (fun c => ∫ x, ‖f c x‖^2 ∂μ) l (nhds 0))
    (htg : Tendsto (fun c => ∫ x, ‖g c x‖^2 ∂μ) l (nhds 0)) :
    Tendsto (fun c => ∫ x, ‖f c x + g c x‖^2 ∂μ) l (nhds 0) := by
  have hb : ∀ᶠ c in l, (∫ x, ‖f c x + g c x‖^2 ∂μ) ≤
      2 * ((∫ x, ‖f c x‖^2 ∂μ) + ∫ x, ‖g c x‖^2 ∂μ) := by
    filter_upwards [hf,hg,hcf,hcg] with c hfc hgc hcfc hcgc
    exact integral_add_square_le _ _ hfc hgc hcfc hcgc
  have ht := (htf.add htg).const_mul 2
  exact squeeze_zero' (Eventually.of_forall (fun c => integral_nonneg (fun x => sq_nonneg _))) hb (by simpa using ht)

theorem cutoff_square_tendsto_zero [Nonempty E] (η : E → ℝ) (hη : Continuous η) (hcη : HasCompactSupport η)
    (f : ι → E → ℝ) (hf : ∀ᶠ c in l, Continuous (f c))
    (hfi : ∀ᶠ c in l, Integrable (fun x => ‖f c x‖^2) μ)
    (htf : Tendsto (fun c => ∫ x, ‖f c x‖^2 ∂μ) l (nhds 0)) :
    Tendsto (fun c => ∫ x, ‖η x * f c x‖^2 ∂μ) l (nhds 0) := by
  obtain ⟨M,hM,hMb⟩ := CompactScalarBound.exists_bound η hη hcη
  have hb : ∀ᶠ c in l, (∫ x, ‖η x * f c x‖^2 ∂μ) ≤ M^2 * ∫ x, ‖f c x‖^2 ∂μ := by
    filter_upwards [hf,hfi] with c hfc hfic
    exact cutoff_square_le η (f c) hη hcη hfc hfic M hM hMb
  exact squeeze_zero' (Eventually.of_forall (fun c => integral_nonneg (fun x => sq_nonneg _))) hb
    (by simpa using htf.const_mul (M^2))

end TernaryPoly.CompactSquareIntegral
