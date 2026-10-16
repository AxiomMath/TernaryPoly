module

public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.Completion
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion

@[expose] public section


/-! Bounded maps out of the actual compact pairing core extend to its completion. -/
noncomputable section
namespace TernaryPoly.CompactPairingCompletion
open MeasureTheory
variable {X V F : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (d : Data X V)

def targetCoreLinear (L : V →ₗ[ℝ] F) : Space μ d →ₗ[ℝ] F where
  toFun := fun v => L v
  map_add' := L.map_add
  map_smul' := L.map_smul

def targetCoreContinuous (L : V →ₗ[ℝ] F) (C : ℝ)
    (hL : ∀ v : V, ‖L v‖ ≤ C * ‖inclusion μ d v‖) : Space μ d →L[ℝ] F :=
  (targetCoreLinear μ d L).mkContinuous C (by
    intro v
    exact (hL v).trans_eq (congrArg (C * ·) ((inclusion μ d).norm_map v)))

def boundedTargetExtension (L : V →ₗ[ℝ] F) (C : ℝ)
    (hL : ∀ v : V, ‖L v‖ ≤ C * ‖inclusion μ d v‖) : Hilbert μ d →L[ℝ] F :=
  (targetCoreContinuous μ d L C hL).fromCompletion

theorem boundedTargetExtension_inclusion (L : V →ₗ[ℝ] F) (C : ℝ)
    (hL : ∀ v : V, ‖L v‖ ≤ C * ‖inclusion μ d v‖) (v : V) :
    boundedTargetExtension μ d L C hL (inclusion μ d v) = L v :=
  ContinuousLinearMap.fromCompletion_apply_coe (targetCoreContinuous μ d L C hL) v

end TernaryPoly.CompactPairingCompletion
