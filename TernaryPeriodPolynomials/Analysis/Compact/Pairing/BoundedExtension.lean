module

public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.Completion
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion

@[expose] public section

/-! Actual bounded extension from the compact pairing core to its literal Hilbert completion. -/
noncomputable section
namespace TernaryPoly.CompactPairingCompletion
open MeasureTheory
variable {X V : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [AddCommGroup V] [Module ℝ V]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (d : Data X V)

def coreLinear (L : V →ₗ[ℝ] V) : Space μ d →ₗ[ℝ] Space μ d where
  toFun := fun v => L v
  map_add' := L.map_add
  map_smul' := L.map_smul

def coreContinuous (L : V →ₗ[ℝ] V) (C : ℝ)
    (hL : ∀ v : V, ‖inclusion μ d (L v)‖ ≤ C * ‖inclusion μ d v‖) :
    Space μ d →L[ℝ] Hilbert μ d :=
  (((inclusion μ d).toLinearMap).comp (coreLinear μ d L)).mkContinuous C (by
    intro v
    exact (hL v).trans_eq (congrArg (C * ·) ((inclusion μ d).norm_map v)))

/-- A concrete core operator extends to the actual completion via its proved norm bound. -/
def boundedExtension (L : V →ₗ[ℝ] V) (C : ℝ)
    (hL : ∀ v : V, ‖inclusion μ d (L v)‖ ≤ C * ‖inclusion μ d v‖) :
    Hilbert μ d →L[ℝ] Hilbert μ d := (coreContinuous μ d L C hL).fromCompletion

theorem boundedExtension_inclusion (L : V →ₗ[ℝ] V) (C : ℝ)
    (hL : ∀ v : V, ‖inclusion μ d (L v)‖ ≤ C * ‖inclusion μ d v‖) (v : V) :
    boundedExtension μ d L C hL (inclusion μ d v) = inclusion μ d (L v) :=
  ContinuousLinearMap.fromCompletion_apply_coe (coreContinuous μ d L C hL) v

end TernaryPoly.CompactPairingCompletion
