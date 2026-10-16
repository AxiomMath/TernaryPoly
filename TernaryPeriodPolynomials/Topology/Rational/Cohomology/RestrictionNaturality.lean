module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
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

namespace TernaryPoly.RationalCohomologyRestriction
open CategoryTheory Rep

variable {G : Type} [Group G] (H : Subgroup G) (A : Rep.{0} ℚ G)

/-- Restrict an explicit coefficient intertwiner along a commuting subgroup square. -/
def restrictedIntertwiner (f : G →* G) (g : H →* H)
    (hfg : ∀ x : H, f x = (g x : G)) (φ : Rep.res f A ⟶ A) :
    Rep.res g (Rep.res H.subtype A) ⟶ Rep.res H.subtype A :=
  Rep.ofHom ⟨φ.hom.toLinearMap, fun x => by
    change φ.hom.toLinearMap ∘ₗ A.ρ (g x : G) = A.ρ (x : G) ∘ₗ φ.hom.toLinearMap
    have h := φ.hom.isIntertwining' (x : G)
    change φ.hom.toLinearMap ∘ₗ A.ρ (f x) = A.ρ (x : G) ∘ₗ φ.hom.toLinearMap at h
    rw [hfg x] at h
    exact h⟩

/-- Actual restriction commutes with a group endomorphism preserving the subgroup,
with the coefficient intertwiner retained explicitly. -/
theorem restriction_naturality (f : G →* G) (g : H →* H)
    (hfg : ∀ x : H, f x = (g x : G)) (φ : Rep.res f A ⟶ A) (n : ℕ) :
    groupCohomology.map f φ n ≫ groupCohomology.map H.subtype (𝟙 _) n =
      groupCohomology.map H.subtype (𝟙 _) n ≫
        groupCohomology.map g (restrictedIntertwiner H A f g hfg φ) n := by
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext x
    exact hfg x
  · rfl

/-- An invariant actual cohomology class remains invariant after restriction.
In particular this applies to normalizing automorphisms; finite index and
semisimplicity are not needed for naturality. -/
theorem restriction_preserves_invariant (f : G →* G) (g : H →* H)
    (hfg : ∀ x : H, f x = (g x : G)) (φ : Rep.res f A ⟶ A) (n : ℕ)
    (x : groupCohomology A n) (hx : groupCohomology.map f φ n x = x) :
    groupCohomology.map g (restrictedIntertwiner H A f g hfg φ) n
        (groupCohomology.map H.subtype (𝟙 _) n x) =
      groupCohomology.map H.subtype (𝟙 _) n x := by
  have h := congrArg (fun t => t x) (restriction_naturality H A f g hfg φ n)
  simpa only [ModuleCat.comp_apply, hx] using h.symm

/-- The actual automorphism of a subgroup preserved by an ambient automorphism. -/
def subgroupAutomorphism (α : G ≃* G) (hα : ∀ x : G, x ∈ H ↔ α x ∈ H) : H ≃* H where
  toFun x := ⟨α x, (hα x).mp x.property⟩
  invFun x := ⟨α.symm x, (hα (α.symm x)).mpr (by rw [α.apply_symm_apply]; exact x.property)⟩
  left_inv x := Subtype.ext (α.symm_apply_apply x)
  right_inv x := Subtype.ext (α.apply_symm_apply x)
  map_mul' x y := Subtype.ext (α.map_mul x y)

/-- Normalizer equivariance of actual finite-index restriction, with no
semisimplicity hypothesis and with the actual coefficient intertwiner explicit. -/
theorem restriction_normalizer_naturality (α : G ≃* G)
    (hα : ∀ x : G, x ∈ H ↔ α x ∈ H) (φ : Rep.res α.toMonoidHom A ⟶ A) (n : ℕ) :
    groupCohomology.map α.toMonoidHom φ n ≫ groupCohomology.map H.subtype (𝟙 _) n =
      groupCohomology.map H.subtype (𝟙 _) n ≫
        groupCohomology.map (subgroupAutomorphism H α hα).toMonoidHom
          (restrictedIntertwiner H A α.toMonoidHom (subgroupAutomorphism H α hα).toMonoidHom
            (fun _ => rfl) φ) n :=
  restriction_naturality H A α.toMonoidHom (subgroupAutomorphism H α hα).toMonoidHom
    (fun _ => rfl) φ n

end TernaryPoly.RationalCohomologyRestriction
