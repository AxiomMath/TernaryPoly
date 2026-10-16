module

public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.BoundedExtension

@[expose] public section


/-! The actual completion extension preserves its proved core norm bound. -/
noncomputable section
namespace TernaryPoly.CompactPairingCompletion
open MeasureTheory
variable {X V : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [AddCommGroup V] [Module ℝ V]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (d : Data X V)

theorem boundedExtension_bound (L : V →ₗ[ℝ] V) (C : ℝ)
    (hL : ∀ v : V, ‖inclusion μ d (L v)‖ ≤ C * ‖inclusion μ d v‖) (w : Hilbert μ d) :
    ‖boundedExtension μ d L C hL w‖ ≤ C * ‖w‖ := by
  refine (denseRange_inclusion μ d).induction_on
    (p := fun z => ‖boundedExtension μ d L C hL z‖ ≤ C * ‖z‖) w
    (isClosed_le (boundedExtension μ d L C hL).continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro v
  rw [boundedExtension_inclusion μ d L C hL v]
  exact hL v

theorem boundedExtension_opNorm_le (L : V →ₗ[ℝ] V) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ v : V, ‖inclusion μ d (L v)‖ ≤ C * ‖inclusion μ d v‖) :
    ‖boundedExtension μ d L C hL‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (boundedExtension_bound μ d L C hL)

end TernaryPoly.CompactPairingCompletion
