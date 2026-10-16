module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Group.MinimalAxioms
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
namespace TernaryPoly.FreeGroupSecondCohomology
open CategoryTheory CategoryTheory.Limits groupCohomology

variable {G : Type} [Group G] (A : Rep ℚ G) (c : cocycles₂ A)

/-- The genuine extension group associated to an arbitrary, possibly unnormalized, two-cocycle. -/
def Extension (_c : cocycles₂ A) := A × G

instance : Mul (Extension A c) := ⟨fun x y => (x.1+A.ρ x.2 y.1+c (x.2,y.2),x.2*y.2)⟩
instance : One (Extension A c) := ⟨(-c (1,1),1)⟩
instance : Inv (Extension A c) := ⟨fun x => (-A.ρ x.2⁻¹ x.1-c (x.2⁻¹,x.2)-c (1,1),x.2⁻¹)⟩

instance : Group (Extension A c) := Group.ofLeftAxioms
  (by
    rintro ⟨a,g⟩ ⟨b,h⟩ ⟨d,j⟩
    apply Prod.ext
    · change (a+A.ρ g b+c (g,h))+A.ρ (g*h) d+c (g*h,j)=
        a+A.ρ g (b+A.ρ h d+c (h,j))+c (g,h*j)
      have hc := (mem_cocycles₂_iff c).mp c.property g h j
      rw [map_add,map_add,←Module.End.mul_apply,←map_mul]
      calc
        _=a+A.ρ g b+A.ρ (g*h) d+(c (g*h,j)+c (g,h)) := by abel
        _=a+A.ρ g b+A.ρ (g*h) d+(A.ρ g (c (h,j))+c (g,h*j)) := by rw [hc]
        _=_ := by abel
    · exact mul_assoc g h j)
  (by
    rintro ⟨a,g⟩
    apply Prod.ext
    · change -c (1,1)+A.ρ 1 a+c (1,g)=a
      rw [map_one,Module.End.one_apply,cocycles₂_map_one_fst c g]
      abel
    · exact one_mul g)
  (by
    rintro ⟨a,g⟩
    apply Prod.ext
    · change (-A.ρ g⁻¹ a-c (g⁻¹,g)-c (1,1))+A.ρ g⁻¹ a+c (g⁻¹,g)= -c (1,1)
      abel
    · exact inv_mul_cancel g)

/-- The literal second-coordinate projection of the cocycle extension. -/
def projection : Extension A c →* G where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' _ _ := rfl

variable {I : Type} (B : Rep ℚ (FreeGroup I)) (d : cocycles₂ B)

/-- The chosen literal lift of each free generator. -/
def generatorLift (i : I) : Extension B d := (0,FreeGroup.of i)

/-- Freeness splits the genuine cocycle extension. -/
def splitting : FreeGroup I →* Extension B d :=
  FreeGroup.lift (generatorLift B d)

theorem projection_splitting (g : FreeGroup I) : projection B d (splitting B d g)=g := by
  have he : (projection B d).comp (splitting B d)=MonoidHom.id (FreeGroup I) := by
    apply FreeGroup.lift.symm.injective
    funext i
    change projection B d (splitting B d (FreeGroup.of i))=FreeGroup.of i
    rw [splitting,FreeGroup.lift_apply_of]
    rfl
  exact DFunLike.congr_fun he g

/-- The first coordinate of a free splitting is an actual coboundary primitive. -/
theorem cocycle_is_coboundary : ⇑d ∈ coboundaries₂ B := by
  change ⇑d ∈ LinearMap.range (d₁₂ B).hom
  refine ⟨fun g => -(splitting B d g).1,?_⟩
  funext x
  rcases x with ⟨g,h⟩
  have he := congrArg (fun x : Extension B d => x.1) ((splitting B d).map_mul g h)
  change (splitting B d (g*h)).1=(splitting B d g).1+
    B.ρ ((splitting B d g).2) ((splitting B d h).1)+d ((splitting B d g).2,(splitting B d h).2) at he
  have hg : (splitting B d g).2=g := projection_splitting B d g
  have hh : (splitting B d h).2=h := projection_splitting B d h
  rw [hg,hh] at he
  simp only [d₁₂_hom_apply,map_neg]
  rw [he]
  abel

/-- Genuine second cohomology of every free group with arbitrary rational coefficients is zero. -/
theorem isZero_H2 : IsZero (groupCohomology B 2) := by
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  have hz (x : groupCohomology B 2) : x=0 := by
    induction x using H2_induction_on with
    | h d => exact (H2π_eq_zero_iff d).mpr (cocycle_is_coboundary B d)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end TernaryPoly.FreeGroupSecondCohomology
