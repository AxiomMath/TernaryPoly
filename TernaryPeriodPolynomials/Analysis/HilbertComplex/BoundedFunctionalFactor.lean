module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
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
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section

/-! A bounded functional on the image of an arbitrary linear map has a Riesz representative. -/
namespace TernaryPoly.HilbertBoundedFunctional

variable {G E : Type*} [AddCommGroup G] [Module ℝ G]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The source needs no topology. The image estimate supplies exactly the
continuity needed to descend, extend, and apply Riesz representation. -/
theorem exists_inner_factor (A : G →ₗ[ℝ] E) (φ : G →ₗ[ℝ] ℝ) (C : ℝ)
    (hb : ∀ x, ‖φ x‖ ≤ C * ‖A x‖) :
    ∃ v : E, ∀ x, inner ℝ v (A x) = φ x := by
  have hk : A.ker ≤ φ.ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [LinearMap.mem_ker.mp hx, norm_zero, mul_zero] using hb x
  let l : A.range →ₗ[ℝ] ℝ :=
    (A.ker.liftQ φ hk).comp A.quotKerEquivRange.symm.toLinearMap
  have hl (x : G) (hx : A x ∈ A.range) : l ⟨A x, hx⟩ = φ x := by
    dsimp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hlb (y : A.range) : ‖l y‖ ≤ C * ‖y‖ := by
    obtain ⟨x, hx⟩ := y.property
    have he : y = ⟨A x, LinearMap.mem_range_self A x⟩ := Subtype.ext hx.symm
    rw [he, hl]
    exact hb x
  let lc : A.range →L[ℝ] ℝ := l.mkContinuous C hlb
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq A.range lc
  refine ⟨(InnerProductSpace.toDual ℝ E).symm g, fun x => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact (hg ⟨A x, LinearMap.mem_range_self A x⟩).trans (hl x _)

end TernaryPoly.HilbertBoundedFunctional
