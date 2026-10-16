module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
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
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section

namespace TernaryPoly.RationalCohomologyRestriction
open CategoryTheory Opposite

variable {G : Type} [Group G]

/-- Precomposition on the literal complex of equivariant morphisms. -/
def resolutionPrecomp {P Q : ChainComplex (Rep.{0} ℚ G) ℕ} (f : P ⟶ Q) (A : Rep.{0} ℚ G) :
    Q.linearYonedaObj ℚ A ⟶ P.linearYonedaObj ℚ A where
  f i := ModuleCat.ofHom
    { toFun x := f.f i ≫ x
      map_add' x y := by simp only [Preadditive.comp_add]
      map_smul' r x := by simp only [Linear.comp_smul, RingHom.id_apply] }
  comm' i j _ := by
    ext x
    change Q.X i ⟶ A at x
    change P.d j i ≫ f.f i ≫ x = f.f j ≫ Q.d j i ≫ x
    simpa only [Category.assoc] using
      congrArg (fun u : P.X j ⟶ Q.X i => u ≫ x) (f.comm j i).symm

/-- Precomposition has the expected compatibility with the opposite homology comparison. -/
theorem resolutionPrecomp_homologyUnop {P Q : ChainComplex (Rep.{0} ℚ G) ℕ}
    (f : P ⟶ Q) (A : Rep.{0} ℚ G) (n : ℕ) :
    (HomologicalComplex.homologyUnop
      ((((linearYoneda ℚ (Rep.{0} ℚ G)).obj A).rightOp.mapHomologicalComplex _).obj Q) n).inv ≫
        HomologicalComplex.homologyMap (resolutionPrecomp f A) n =
      (HomologicalComplex.homologyMap
        ((((linearYoneda ℚ (Rep.{0} ℚ G)).obj A).rightOp.mapHomologicalComplex _).map f) n).unop ≫
      (HomologicalComplex.homologyUnop
        ((((linearYoneda ℚ (Rep.{0} ℚ G)).obj A).rightOp.mapHomologicalComplex _).obj P) n).inv := by
  have h := HomologicalComplex.homologyOp_hom_naturality (resolutionPrecomp f A) n
  let F := ((linearYoneda ℚ (Rep.{0} ℚ G)).obj A).rightOp.mapHomologicalComplex
    (ComplexShape.down ℕ)
  let t : (F.obj Q).unop.homology n ⟶ (F.obj P).unop.homology n :=
    HomologicalComplex.homologyMap (resolutionPrecomp f A) n
  change (HomologicalComplex.homologyUnop (F.obj Q) n).inv ≫ t =
    (HomologicalComplex.homologyMap (F.map f) n).unop ≫
      (HomologicalComplex.homologyUnop (F.obj P) n).inv
  have hu : (HomologicalComplex.homologyUnop (F.obj Q) n).hom ≫
      (HomologicalComplex.homologyMap (F.map f) n).unop =
      t ≫ (HomologicalComplex.homologyUnop (F.obj P) n).hom :=
    congrArg Quiver.Hom.unop h
  rw [← cancel_mono (HomologicalComplex.homologyUnop (F.obj P) n).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hu, Iso.inv_hom_id_assoc]

/-- A comparison of projective resolutions lifting the identity induces the
canonical Ext comparison used by Mathlib's Shapiro isomorphism. -/
theorem isoExt_precomp {X : Rep.{0} ℚ G} (P Q : ProjectiveResolution X)
    (f : P.complex ⟶ Q.complex)
    (hf : f.f 0 ≫ Q.π.f 0 = P.π.f 0) (A : Rep.{0} ℚ G) (n : ℕ) :
    (Q.isoExt n A).hom ≫ HomologicalComplex.homologyMap (resolutionPrecomp f A) n =
      (P.isoExt n A).hom := by
  have h := ProjectiveResolution.isoLeftDerivedObj_inv_naturality (𝟙 X) P Q f
    (hf.trans (Category.comp_id _).symm) ((linearYoneda ℚ (Rep.{0} ℚ G)).obj A).rightOp n
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  have hu := congrArg Quiver.Hom.unop h
  simp only [unop_comp] at hu
  let F := ((linearYoneda ℚ (Rep.{0} ℚ G)).obj A).rightOp
  let FF := F.mapHomologicalComplex (ComplexShape.down ℕ)
  let hp := HomologicalComplex.homologyUnop (FF.obj P.complex) n
  let hq := HomologicalComplex.homologyUnop (FF.obj Q.complex) n
  let t : (FF.obj Q.complex).unop.homology n ⟶ (FF.obj P.complex).unop.homology n :=
    HomologicalComplex.homologyMap (resolutionPrecomp f A) n
  have ht : hq.inv ≫ t =
      (HomologicalComplex.homologyMap (FF.map f) n).unop ≫ hp.inv :=
    resolutionPrecomp_homologyUnop f A n
  let pm : unop ((F.leftDerived n).obj X) ⟶ unop ((FF.obj P.complex).homology n) :=
    (P.isoLeftDerivedObj F n).inv.unop
  let qm : unop ((F.leftDerived n).obj X) ⟶ unop ((FF.obj Q.complex).homology n) :=
    (Q.isoLeftDerivedObj F n).inv.unop
  have hu' : pm = qm ≫
        (HomologicalComplex.homologyMap (FF.map f) n).unop := hu
  have he : (qm ≫ hq.inv) ≫ t = pm ≫ hp.inv := by
    rw [Category.assoc, ht, ← Category.assoc, ← hu']
  exact he

end TernaryPoly.RationalCohomologyRestriction
