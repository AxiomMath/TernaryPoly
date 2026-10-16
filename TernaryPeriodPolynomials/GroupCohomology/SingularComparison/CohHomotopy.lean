module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
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


/-!
# `Hom(-, A)` of a chain map of projective resolutions is a quasi-isomorphism

Formalized by Claude Sonnet 5.5.

For chain complexes `P, Q` of representations of `H` and a chain map `φ : P ⟶ Q`, `yMap φ A` is the
precomposition `Hom(Q, A) ⟶ Hom(P, A)` of cochain complexes (`yMap_apply`).  If `P`, `Q` are projective
resolutions of the same representation and `φ` is compatible with the augmentations, then `φ` is a homotopy
equivalence (`resHomotopyEquiv`, from `ProjectiveResolution.liftHomotopy`), hence `yMap φ A` induces
isomorphisms on all cohomology groups (`isIso_homologyMap_yMap_res`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HomologyBridge

open CategoryTheory Representation MonoidalCategory

universe u

section Y

variable {H : Type} [Group H]

/-- Precomposition with a chain map: `Hom(Q, A) ⟶ Hom(P, A)`. -/
def yMap {P Q : ChainComplex (Rep ℂ H) ℕ} (φ : P ⟶ Q) (A : Rep ℂ H) :
    Q.linearYonedaObj ℂ A ⟶ P.linearYonedaObj ℂ A :=
  (HomologicalComplex.unopFunctor _ _).map
    ((((linearYoneda ℂ (Rep ℂ H)).obj A).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).map φ).op

theorem yMap_apply {P Q : ChainComplex (Rep ℂ H) ℕ} (φ : P ⟶ Q) (A : Rep ℂ H) (n : ℕ)
    (f : Q.X n ⟶ A) : ((yMap φ A).f n).hom f = φ.f n ≫ f := rfl

@[simp] theorem yMap_comp {P Q R : ChainComplex (Rep ℂ H) ℕ} (φ : P ⟶ Q) (ψ : Q ⟶ R) (A : Rep ℂ H) :
    yMap (φ ≫ ψ) A = yMap ψ A ≫ yMap φ A := by
  unfold yMap
  simp
  rfl

@[simp] theorem yMap_id {P : ChainComplex (Rep ℂ H) ℕ} (A : Rep ℂ H) : yMap (𝟙 P) A = 𝟙 _ := by
  unfold yMap
  simp
  rfl

/-- A homotopy equivalence of chain complexes of representations gives one of the `Hom(-, A)`
complexes. -/
def yHomotopyEquiv {P Q : ChainComplex (Rep ℂ H) ℕ} (e : HomotopyEquiv P Q) (A : Rep ℂ H) :
    HomotopyEquiv (Q.linearYonedaObj ℂ A) (P.linearYonedaObj ℂ A) where
  hom := yMap e.hom A
  inv := yMap e.inv A
  homotopyHomInvId := by
    have h : Homotopy (yMap (e.inv ≫ e.hom) A) (yMap (𝟙 Q) A) :=
      (Functor.mapHomotopy (((linearYoneda ℂ (Rep ℂ H)).obj A).rightOp) e.homotopyInvHomId).unop
    rw [yMap_comp, yMap_id] at h
    exact h
  homotopyInvHomId := by
    have h : Homotopy (yMap (e.hom ≫ e.inv) A) (yMap (𝟙 P) A) :=
      (Functor.mapHomotopy (((linearYoneda ℂ (Rep ℂ H)).obj A).rightOp) e.homotopyHomInvId).unop
    rw [yMap_comp, yMap_id] at h
    exact h

theorem isIso_homologyMap_yMap {P Q : ChainComplex (Rep ℂ H) ℕ} (e : HomotopyEquiv P Q)
    (A : Rep ℂ H) (n : ℕ) : IsIso (HomologicalComplex.homologyMap (yMap e.hom A) n) := by
  have := (yHomotopyEquiv e A).quasiIsoAt_hom n
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp this

/-- A chain map between projective resolutions over the identity is a homotopy equivalence. -/
def resHomotopyEquiv {X : Rep ℂ H} (P Q : ProjectiveResolution X) (φ : P.complex ⟶ Q.complex)
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) : HomotopyEquiv P.complex Q.complex where
  hom := φ
  inv := ProjectiveResolution.lift (𝟙 X) Q P
  homotopyHomInvId := by
    have hφ' : φ ≫ Q.π = P.π := by
      refine HomologicalComplex.to_single_hom_ext ?_
      simpa using hφ
    refine ProjectiveResolution.liftHomotopy (𝟙 X) _ _ ?_ ?_
    · rw [Category.assoc, ProjectiveResolution.lift_commutes, ← Category.assoc, hφ']
    · simp
  homotopyInvHomId := by
    have hφ' : φ ≫ Q.π = P.π := by
      refine HomologicalComplex.to_single_hom_ext ?_
      simpa using hφ
    refine ProjectiveResolution.liftHomotopy (𝟙 X) _ _ ?_ ?_
    · rw [Category.assoc, hφ', ProjectiveResolution.lift_commutes]
    · simp

theorem isIso_homologyMap_yMap_res {X : Rep ℂ H} (P Q : ProjectiveResolution X)
    (φ : P.complex ⟶ Q.complex) (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (A : Rep ℂ H) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (yMap φ A) n) :=
  isIso_homologyMap_yMap (resHomotopyEquiv P Q φ hφ) A n

end Y

end TernaryPeriodPolynomials.Argument.HomologyBridge
