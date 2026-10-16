module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanBoxBasis
open TopologicalSpace Set

variable {ι : Type}

/-- A coordinate box, allowing empty coordinate intervals. -/
def box (l u : ι → ℝ) : Set (ι → ℝ) := {x | ∀ i, l i < x i ∧ x i < u i}

/-- The collection of all coordinate boxes. -/
def boxes : Set (Set (ι → ℝ)) := {s | ∃ l u, s = box l u}

theorem box_isOpen [Fintype ι] (l u : ι → ℝ) : IsOpen (box l u) := by
  have he : box l u = ⋂ i, {x : ι → ℝ | l i < x i ∧ x i < u i} := by
    ext x
    simp [box]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_apply i) continuous_const)

theorem box_inter (l u l' u' : ι → ℝ) :
    box l u ∩ box l' u' = box (fun i => max (l i) (l' i)) (fun i => min (u i) (u' i)) := by
  ext x
  simp only [box, mem_inter_iff, mem_ofPred_eq, max_lt_iff, lt_min_iff]
  aesop

theorem boxes_inter : ∀ b ∈ (boxes : Set (Set (ι → ℝ))), ∀ c ∈ boxes, b ∩ c ∈ boxes := by
  rintro b ⟨l,u,rfl⟩ c ⟨l',u',rfl⟩
  exact ⟨_,_,box_inter l u l' u'⟩

/-- The coordinate boxes form a basis for the usual finite product topology. -/
theorem boxes_basis [Fintype ι] : IsTopologicalBasis (boxes : Set (Set (ι → ℝ))) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro b ⟨l,u,rfl⟩
    exact box_isOpen l u
  · intro x s hx hs
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hs x hx
    refine ⟨box (fun i => x i - ε) (fun i => x i + ε), ⟨_,_,rfl⟩, ?_, ?_⟩
    · intro i
      constructor <;> linarith
    · intro y hy
      apply hball
      apply (dist_pi_lt_iff hε).2
      intro i
      rw [Real.dist_eq,abs_lt]
      have hi := hy i
      constructor <;> linarith

/-- A bounded nonempty real interval is homeomorphic to the whole real line. -/
def intervalHomeomorph (a b : ℝ) (hab : a < b) : ℝ ≃ₜ Ioo a b := by
  let c := (b-a)/2
  let d := (a+b)/2
  have hc : 0 < c := by dsimp [c]; linarith
  let h := affineHomeomorph c d hc.ne'
  have he : h '' Ioo (-1 : ℝ) 1 = Ioo a b := by
    rw [affineHomeomorph_image_Ioo _ _ _ _ hc]
    congr 1 <;> dsimp [c,d] <;> ring
  exact (orderIsoIooNegOneOne ℝ).toHomeomorph.trans ((h.image _).trans (Homeomorph.setCongr he))

/-- The subtype of a coordinate box is the product of its coordinate interval subtypes. -/
def boxProductHomeomorph (l u : ι → ℝ) : box l u ≃ₜ (∀ i, Ioo (l i) (u i)) where
  toFun x i := ⟨x.val i, x.property i⟩
  invFun x := ⟨fun i => (x i).val, fun i => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi (fun i => ((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := by fun_prop

/-- Every box with strictly ordered endpoints is homeomorphic to the entire finite product. -/
def boxHomeomorph (l u : ι → ℝ) (h : ∀ i, l i < u i) : box l u ≃ₜ (ι → ℝ) :=
  (boxProductHomeomorph l u).trans (Homeomorph.piCongrRight fun i => (intervalHomeomorph (l i) (u i) (h i)).symm)

/-- Nonempty boxes admit the required genuine homeomorphism to the finite product. -/
theorem box_nonempty_homeomorph (l u : ι → ℝ) (h : (box l u).Nonempty) :
    Nonempty (box l u ≃ₜ (ι → ℝ)) := by
  obtain ⟨x,hx⟩ := h
  exact ⟨boxHomeomorph l u (fun i => lt_trans (hx i).1 (hx i).2)⟩

end TernaryPoly.EuclideanBoxBasis
