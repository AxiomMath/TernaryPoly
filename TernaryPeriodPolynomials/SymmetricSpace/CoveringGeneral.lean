module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
open Topology Set
namespace TernaryPoly.SymmetricSpaceCovering

variable {G E : Type*} [Group G] [TopologicalSpace E] [MulAction G E]
  [ContinuousConstSMul G E] [LocallyCompactSpace E] [T2Space E]

/-- A free action with finite actual compact transporters has a genuine orbit covering. -/
theorem quotientCovering_of_finite_transporters
    (hfinite : ∀ (C D : Set E), IsCompact C → IsCompact D →
      {g : G | ((g • ·) '' C ∩ D).Nonempty}.Finite)
    (hfree : ∀ (g : G) (x : E), g • x=x → g=1) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G E)) G := by
  let : ProperlyDiscontinuousSMul G E := ⟨fun hC hD => hfinite _ _ hC hD⟩
  let : IsCancelSMul G E := isCancelSMul_iff_eq_one_of_smul_eq.mpr hfree
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- Explicit open neighborhoods meet no nontrivial translate of themselves. -/
theorem exists_open_disjoint_translates
    (hfinite : ∀ (C D : Set E), IsCompact C → IsCompact D →
      {g : G | ((g • ·) '' C ∩ D).Nonempty}.Finite)
    (hfree : ∀ (g : G) (x : E), g • x=x → g=1) (x : E) :
    ∃ U : Set E, IsOpen U ∧ x∈U ∧ ∀ g : G, g≠1 → Disjoint ((g • ·) '' U) U := by
  obtain ⟨V,hV,hd⟩ := (quotientCovering_of_finite_transporters hfinite hfree).disjoint x
  refine ⟨interior V,isOpen_interior,mem_interior_iff_mem_nhds.mpr hV,?_⟩
  intro g hg
  apply Set.disjoint_left.mpr
  intro y hy hyU
  obtain ⟨z,hz,rfl⟩ := hy
  exact hg (hd g ⟨g • z,⟨z,interior_subset hz,rfl⟩,interior_subset hyU⟩)

/-- The orbit projection is a covering map in Mathlib's actual topological sense. -/
theorem covering_of_finite_transporters
    (hfinite : ∀ (C D : Set E), IsCompact C → IsCompact D →
      {g : G | ((g • ·) '' C ∩ D).Nonempty}.Finite)
    (hfree : ∀ (g : G) (x : E), g • x=x → g=1) :
    IsCoveringMap (Quotient.mk (MulAction.orbitRel G E)) :=
  (quotientCovering_of_finite_transporters hfinite hfree).isCoveringMap

/-- Finite compact transporters also give Hausdorffness of the actual orbit quotient. -/
theorem quotient_t2_of_finite_transporters
    (hfinite : ∀ (C D : Set E), IsCompact C → IsCompact D →
      {g : G | ((g • ·) '' C ∩ D).Nonempty}.Finite) :
    T2Space (Quotient (MulAction.orbitRel G E)) := by
  let : ProperlyDiscontinuousSMul G E := ⟨fun hC hD => hfinite _ _ hC hD⟩
  infer_instance

end TernaryPoly.SymmetricSpaceCovering
