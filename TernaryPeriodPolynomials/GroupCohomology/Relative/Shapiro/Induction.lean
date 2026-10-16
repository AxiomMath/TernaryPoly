module

public import Mathlib.RepresentationTheory.Induced
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.Perm.Option
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
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeShapiroInduction
open CategoryTheory Representation Finsupp TensorProduct

variable {G : Type} [Group G] (H : Subgroup G)
abbrev RightCosets := Quotient (QuotientGroup.rightRel H)

def coset (g : G) : RightCosets H := Quotient.mk (QuotientGroup.rightRel H) g

def representative (q : RightCosets H) : G := q.out

lemma representative_coset (q : RightCosets H) : coset H (representative H q) = q :=
  Quotient.out_eq q

lemma coset_mul (s : H) (g : G) : coset H (s.1 * g) = coset H g :=
  Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp [mul_inv_rev]))

/-- The unique subgroup factor relative to the chosen right-coset representative. -/
def factor (g : G) : H := ⟨g * (representative H (coset H g))⁻¹, by
  apply QuotientGroup.rightRel_apply.mp
  exact Quotient.exact (representative_coset H (coset H g))⟩

lemma factor_mul (s : H) (g : G) : factor H (s.1 * g) = s * factor H g := by
  apply Subtype.ext
  simp [factor, coset_mul, mul_assoc]

lemma factor_rep (q : RightCosets H) : factor H (representative H q) = 1 := by
  apply Subtype.ext
  simp [factor, representative_coset]

lemma factor_mul_rep (g : G) : (factor H g).1 * representative H (coset H g) = g := by
  simp [factor, mul_assoc]

variable (A : Rep.{0} ℚ H)

/-- The coset-coordinate map on the generators of induction. -/
def coordinateGenerator (g : G) : A →ₗ[ℚ] (RightCosets H →₀ A) :=
  (Finsupp.lsingle (coset H g)).comp (A.ρ (factor H g)⁻¹)

lemma coordinateGenerator_mul (s : H) (g : G) (a : A) :
    coordinateGenerator H A (s.1 * g) (A.ρ s a) = coordinateGenerator H A g a := by
  simp [coordinateGenerator, factor_mul, coset_mul, mul_inv_rev, map_mul,
    Module.End.mul_apply]

/-- Explicit coordinates of induction as a direct sum over right cosets. -/
def coordinates : Rep.ind H.subtype A →ₗ[ℚ] (RightCosets H →₀ A) :=
  Coinvariants.lift _
    (TensorProduct.lift ((Finsupp.lift _ ℚ G (coordinateGenerator H A)).comp
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)) (fun s => by
        ext g a
        simpa [Representation.ofMulAction_single] using
          congrArg (fun f : RightCosets H →₀ A => f _) (coordinateGenerator_mul H A s g a))

@[simp]
lemma coordinates_mk (g : G) (a : A) :
    coordinates H A (IndV.mk H.subtype A.ρ g a) =
      Finsupp.single (coset H g) (A.ρ (factor H g)⁻¹ a) := by
  simp [coordinates, IndV.mk, coordinateGenerator]

/-- Reassemble the actual induced representation from its finite coset coordinates. -/
def fromCoordinates : (RightCosets H →₀ A) →ₗ[ℚ] Rep.ind H.subtype A :=
  Finsupp.lsum ℚ (fun q => IndV.mk H.subtype A.ρ (representative H q))

@[simp]
lemma fromCoordinates_single (q : RightCosets H) (a : A) :
    fromCoordinates H A (Finsupp.single q a) =
      IndV.mk H.subtype A.ρ (representative H q) a := by
  simp [fromCoordinates]

lemma coordinates_fromCoordinates :
    (coordinates H A).comp (fromCoordinates H A) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro q a
  change coordinates H A (fromCoordinates H A (single q a)) = single q a
  rw [fromCoordinates_single, coordinates_mk, representative_coset, factor_rep]
  simp

lemma fromCoordinates_coordinates :
    (fromCoordinates H A).comp (coordinates H A) = LinearMap.id := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change fromCoordinates H A (coordinates H A (IndV.mk H.subtype A.ρ g a)) =
    IndV.mk H.subtype A.ρ g a
  rw [coordinates_mk, fromCoordinates_single]
  simp [IndV.mk, LinearMap.comp_apply, factor]

/-- The underlying module of subgroup induction is a genuine direct sum over right cosets. -/
def coordinatesEquiv : Rep.ind H.subtype A ≃ₗ[ℚ] (RightCosets H →₀ A) :=
  LinearEquiv.ofLinearMap (coordinates H A) (fromCoordinates H A)
    (coordinates_fromCoordinates H A) (fromCoordinates_coordinates H A)

lemma coordinates_natural {A B : Rep.{0} ℚ H} (f : A ⟶ B) :
    (coordinates H B).comp (Rep.indMap H.subtype f).hom.toLinearMap =
      (Finsupp.mapRange.linearMap f.hom.toLinearMap).comp (coordinates H A) := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change coordinates H B ((Rep.indMap H.subtype f).hom (IndV.mk H.subtype A.ρ g a)) =
    Finsupp.mapRange.linearMap f.hom.toLinearMap (coordinates H A (IndV.mk H.subtype A.ρ g a))
  have hm : (Rep.indMap H.subtype f).hom (IndV.mk H.subtype A.ρ g a) =
      IndV.mk H.subtype B.ρ g (f.hom a) := rfl
  rw [hm, coordinates_mk, coordinates_mk]
  simp [← Rep.hom_comm_apply]

/-- Subgroup induction preserves monomorphisms, proved in its actual coset coordinates. -/
instance ind_preservesMonomorphisms :
    (Rep.indFunctor.{0} ℚ H.subtype).PreservesMonomorphisms where
  preserves {A B} f := by
    intro hf
    apply (Rep.mono_iff_injective _).mpr
    intro x y hxy
    apply (coordinatesEquiv H A).injective
    apply Finsupp.ext
    intro q
    apply ((Rep.mono_iff_injective f).mp inferInstance)
    have h := congrArg (fun z => coordinates H B z q) hxy
    have hn (z : Rep.ind H.subtype A) :
        coordinates H B ((Rep.indMap H.subtype f).hom z) =
          Finsupp.mapRange.linearMap f.hom.toLinearMap (coordinates H A z) :=
      LinearMap.congr_fun (coordinates_natural H f) z
    change coordinates H B ((Rep.indMap H.subtype f).hom x) q =
      coordinates H B ((Rep.indMap H.subtype f).hom y) q at h
    rw [hn x, hn y] at h
    exact h

instance ind_additive : (Rep.indFunctor.{0} ℚ H.subtype).Additive where
  map_add {_ _ f g} := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply IndV.hom_ext
    intro x
    apply LinearMap.ext
    intro a
    simp [Rep.indFunctor, Rep.indMap, IndV.mk, Rep.add_hom]

/-- Exactness of genuine subgroup induction. -/
instance ind_preservesHomology : (Rep.indFunctor.{0} ℚ H.subtype).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance ind_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (Rep.indFunctor.{0} ℚ H.subtype) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance ind_preservesProjectiveObjects :
    (Rep.indFunctor.{0} ℚ H.subtype).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (Rep.indResAdjunction ℚ H.subtype)

end TernaryPoly.RelativeShapiroInduction
