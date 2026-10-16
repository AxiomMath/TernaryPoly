module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
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
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryCochainNormalization
open CategoryTheory groupCohomology
variable {G : Type} [Group G] (A : Rep ℚ G)

/-- Change a genuine one-cocycle by a genuine zero-cochain coboundary. -/
def normalize (c : cocycles₁ A) (v : A) : cocycles₁ A :=
  c-⟨d₀₁ A v,d₀₁_apply_mem_cocycles₁ v⟩

@[simp] theorem normalize_apply (c : cocycles₁ A) (v : A) (g : G) :
    normalize A c v g=c g-(A.ρ g v-v) := rfl

/-- Literal pullback of a genuine cocycle, retaining the actual restricted representation. -/
def restrict {H : Type} [Group H] (f : H →* G) (c : cocycles₁ A) :
    cocycles₁ (Rep.res f A) :=
  ⟨fun h => c (f h),(mem_cocycles₁_iff _).mpr (by
    intro g h
    simpa using (mem_cocycles₁_iff _).mp c.property (f g) (f h))⟩

@[simp] theorem restrict_apply {H : Type} [Group H] (f : H →* G)
    (c : cocycles₁ A) (h : H) : restrict A f c h=c (f h) := rfl

/-- Normalizing the two actual face representatives changes the compatibility cochain by the
difference of their primitives. This preserves the mapping-cone sign d u = AP - AQ. -/
theorem normalized_corner {P Q B : Type} [Group P] [Group Q] [Group B]
    (iP : P →* G) (iQ : Q →* G) (jP : B →* P) (jQ : B →* Q)
    (hinc : iP.comp jP=iQ.comp jQ)
    (AP : cocycles₁ (Rep.res iP A)) (AQ : cocycles₁ (Rep.res iQ A))
    (u vP vQ : A)
    (hu : ∀ b,A.ρ (iP (jP b)) u-u=AP (jP b)-AQ (jQ b)) :
    ∀ b,A.ρ (iP (jP b)) (u-vP+vQ)-(u-vP+vQ)=
      normalize (Rep.res iP A) AP vP (jP b)-
      normalize (Rep.res iQ A) AQ vQ (jQ b) := by
  intro b
  have hi : iP (jP b)=iQ (jQ b) := DFunLike.congr_fun hinc b
  simp only [map_add,map_sub,normalize_apply]
  change A.ρ (iP (jP b)) u-A.ρ (iP (jP b)) vP+A.ρ (iP (jP b)) vQ-
    (u-vP+vQ) = AP (jP b)-(A.ρ (iP (jP b)) vP-vP)-
      (AQ (jQ b)-(A.ρ (iQ (jQ b)) vQ-vQ))
  rw [←hi,sub_eq_iff_eq_add.mp (hu b)]
  abel

end TernaryPoly.BoundaryCochainNormalization
