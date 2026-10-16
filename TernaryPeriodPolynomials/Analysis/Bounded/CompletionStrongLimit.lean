module

public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! A uniformly bounded operator family converging on the literal completion core converges everywhere. -/
noncomputable section
namespace TernaryPoly.BoundedCompletionStrongLimit
open Filter UniformSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_strong_limit (T : ℕ → Completion E →L[ℝ] F) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ j, ‖T j‖ ≤ C) (f : E → F)
    (hf : ∀ v : E, Tendsto (fun j => T j (v : Completion E)) atTop (nhds (f v))) :
    ∃ L : Completion E →L[ℝ] F,
      (∀ v : E, L (v : Completion E) = f v) ∧
      (∀ x : Completion E, Tendsto (fun j => T j x) atTop (nhds (L x))) := by
  let g (j : ℕ) : E →L[ℝ] F := (T j).comp Completion.toComplL
  have hg : Bornology.IsBounded (Set.range g) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C,?_⟩
    rintro _ ⟨j,rfl⟩
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro v
    exact ((T j).le_opNorm (v : Completion E)).trans
      (by simpa only [Completion.norm_coe] using mul_le_mul_of_nonneg_right (hT j) (norm_nonneg (v : Completion E)))
  have ht : Tendsto (fun j v => g j v) atTop (nhds f) := tendsto_pi_nhds.mpr hf
  let L0 := ContinuousLinearMap.ofTendstoOfBoundedRange f g ht hg
  let L : Completion E →L[ℝ] F := L0.fromCompletion
  have hL (v : E) : L (v : Completion E) = f v := by
    rw [ContinuousLinearMap.fromCompletion_apply_coe]
    exact congrFun (ContinuousLinearMap.ofTendstoOfBoundedRange_apply f g ht hg) v
  refine ⟨L,hL,fun x => ?_⟩
  have heq : Equicontinuous (fun j x => T j x) :=
    (LipschitzWith.uniformEquicontinuous (fun j x => T j x) ⟨C,hC⟩
      (fun j => ContinuousLinearMap.opNorm_le_iff_lipschitz.mp (hT j))).equicontinuous
  refine Completion.denseRange_coe.induction_on x
    (heq.isClosed_setOfPred_tendsto L.continuous) ?_
  intro v
  rw [hL]
  exact hf v

end TernaryPoly.BoundedCompletionStrongLimit
