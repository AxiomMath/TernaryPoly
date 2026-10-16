module

public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
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
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.InwardHomotopyCovering
open scoped unitInterval
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X} (hp : IsCoveringMap p) (H : C(I × X, X))
variable (hzero : ∀ x, H (0, x) = x)

/-- Pull the actual base homotopy back along the covering projection. -/
def baseHomotopy : C(I × E, X) :=
  ⟨fun z => H (z.1, p z.2),
    H.continuous.comp (continuous_fst.prodMk (hp.continuous.comp continuous_snd))⟩

/-- Mathlib's genuine covering-homotopy lift, starting at the identity upstairs. -/
def liftedHomotopy : C(I × E, E) :=
  hp.liftHomotopy (baseHomotopy hp H) (ContinuousMap.id E) (fun e => hzero (p e))

/-- The lifted homotopy projects to the specified base homotopy at every time. -/
theorem liftedHomotopy_projection (t : I) (e : E) :
    p (liftedHomotopy hp H hzero (t, e)) = H (t, p e) :=
  congr_fun (hp.liftHomotopy_lifts (baseHomotopy hp H) (ContinuousMap.id E)
    (fun e => hzero (p e))) (t, e)

@[simp] theorem liftedHomotopy_zero (e : E) : liftedHomotopy hp H hzero (0, e) = e :=
  hp.liftHomotopy_zero (baseHomotopy hp H) (ContinuousMap.id E) (fun e => hzero (p e)) e

variable {U : Set X}

/-- Preservation of the interior downstairs gives preservation of its literal preimage upstairs. -/
theorem liftedHomotopy_preserves (hpres : ∀ t x, x ∈ U → H (t, x) ∈ U)
    (t : I) (e : E) (he : e ∈ p ⁻¹' U) : liftedHomotopy hp H hzero (t, e) ∈ p ⁻¹' U := by
  change p (liftedHomotopy hp H hzero (t, e)) ∈ U
  rw [liftedHomotopy_projection hp H hzero]
  exact hpres t (p e) he

/-- The full endpoint image of the lifted homotopy lies over the designated interior. -/
theorem liftedHomotopy_endpoint (hend : ∀ x, H (1, x) ∈ U) (e : E) :
    liftedHomotopy hp H hzero (1, e) ∈ p ⁻¹' U := by
  change p (liftedHomotopy hp H hzero (1, e)) ∈ U
  rw [liftedHomotopy_projection hp H hzero]
  exact hend (p e)

/-- An interior-preserving base homotopy yields the actual upstairs inclusion homotopy equivalence.
No endpoint-fixing condition on the lifted homotopy, and no openness assumption, is needed. -/
def liftedHomotopyEquiv (hpres : ∀ t x, x ∈ U → H (t, x) ∈ U)
    (hend : ∀ x, H (1, x) ∈ U) : ContinuousMap.HomotopyEquiv (p ⁻¹' U) E where
  toFun := ⟨Subtype.val, continuous_subtype_val⟩
  invFun := ⟨fun e => ⟨liftedHomotopy hp H hzero (1, e),
    liftedHomotopy_endpoint hp H hzero hend e⟩,
    ((liftedHomotopy hp H hzero).continuous.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  left_inv := by
    apply Nonempty.intro
    apply ContinuousMap.Homotopy.symm
    refine ⟨⟨fun z => ⟨liftedHomotopy hp H hzero (z.1, z.2.val),
      liftedHomotopy_preserves hp H hzero hpres z.1 z.2.val z.2.property⟩,
      ((liftedHomotopy hp H hzero).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩, ?_, ?_⟩
    · intro e
      exact Subtype.ext (liftedHomotopy_zero hp H hzero e.val)
    · intro e
      rfl
  right_inv := by
    exact ⟨(⟨liftedHomotopy hp H hzero, liftedHomotopy_zero hp H hzero,
      fun _ => rfl⟩ : ContinuousMap.Homotopy (ContinuousMap.id E) _).symm⟩

@[simp] theorem liftedHomotopyEquiv_apply (hpres : ∀ t x, x ∈ U → H (t, x) ∈ U)
    (hend : ∀ x, H (1, x) ∈ U) (e : p ⁻¹' U) :
    liftedHomotopyEquiv hp H hzero hpres hend e = e.val := rfl

/-- The inverse of the inclusion equivalence is precisely the endpoint of the genuine lift. -/
theorem liftedHomotopyEquiv_invFun (hpres : ∀ t x, x ∈ U → H (t, x) ∈ U)
    (hend : ∀ x, H (1, x) ∈ U) (e : E) :
    ((liftedHomotopyEquiv hp H hzero hpres hend).invFun e).val =
      liftedHomotopy hp H hzero (1, e) := rfl

include hp hzero in
/-- Contractibility of the actual upstairs interior propagates through the constructed equivalence. -/
theorem contractible_of_inward [ContractibleSpace (p ⁻¹' U)]
    (hpres : ∀ t x, x ∈ U → H (t, x) ∈ U) (hend : ∀ x, H (1, x) ∈ U) :
    ContractibleSpace E :=
  (liftedHomotopyEquiv hp H hzero hpres hend).symm.contractibleSpace

end TernaryPoly.InwardHomotopyCovering
