module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.Exact
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
namespace TernaryPoly.RationalHomologyDual
open CategoryTheory Limits HomologicalComplex Opposite

/-- The full rational algebraic dual, on arbitrary vector spaces. No finite-dimensionality is
required: linear functionals extend from every subspace over ℚ. -/
def dualFunctor : (ModuleCat.{0} ℚ)ᵒᵖ ⥤ ModuleCat.{0} ℚ where
  obj V := ModuleCat.of ℚ (Module.Dual ℚ V.unop)
  map f := ModuleCat.ofHom f.unop.hom.dualMap
  map_id _ := by ext φ x; rfl
  map_comp _ _ := by ext φ x; rfl

instance dualFunctor_additive : dualFunctor.Additive where
  map_add := by
    intro X Y f g
    dsimp [dualFunctor]
    ext φ x
    exact map_add φ _ _

/-- Full algebraic dualization is exact over ℚ, including for infinite-dimensional chains. -/
theorem dualFunctor_map_exact (S : ShortComplex ((ModuleCat.{0} ℚ)ᵒᵖ)) (hS : S.Exact) :
    (S.map dualFunctor).Exact := by
  apply ((S.map dualFunctor).moduleCat_exact_iff_range_eq_ker).mpr
  change LinearMap.range S.f.unop.hom.dualMap = LinearMap.ker S.g.unop.hom.dualMap
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  have he := hS.unop.moduleCat_range_eq_ker
  change LinearMap.range S.g.unop.hom = LinearMap.ker S.f.unop.hom at he
  rw [he]

instance dualFunctor_preservesHomology : dualFunctor.PreservesHomology :=
  Functor.preservesHomology_of_map_exact dualFunctor dualFunctor_map_exact

/-- The genuine full linear-dual cochain complex of a rational chain complex. -/
def dualCochains (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) : CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  (dualFunctor.mapHomologicalComplex (ComplexShape.up ℕ)).obj K.op

/-- Its differential is literal precomposition by the singular or algebraic chain boundary. -/
theorem dualCochains_d (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (i j : ℕ) :
    ((dualCochains K).d i j).hom = (K.d j i).hom.dualMap := rfl

/-- The universal-coefficient isomorphism over ℚ identifies full dual cohomology with the
full dual of actual homology, without any finiteness hypothesis. -/
def universalCoefficientIso (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ) :
    (dualCochains K).homology n ≅ ModuleCat.of ℚ (Module.Dual ℚ (K.homology n)) :=
  (K.op.sc n).mapHomologyIso dualFunctor ≪≫ dualFunctor.mapIso (K.homologyOp n)

/-- Full-dual pullback of an actual chain map. -/
def dualMap {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) :
    dualCochains L ⟶ dualCochains K :=
  (dualFunctor.mapHomologicalComplex (ComplexShape.up ℕ)).map
    ((opFunctor _ (ComplexShape.down ℕ)).map f.op)

/-- The universal-coefficient comparison is natural for literal chain maps. -/
theorem universalCoefficientIso_natural {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (f : K ⟶ L) (n : ℕ) :
    homologyMap (dualMap f) n ≫ (universalCoefficientIso K n).hom =
      (universalCoefficientIso L n).hom ≫ ModuleCat.ofHom (homologyMap f n).hom.dualMap := by
  let fo := (opFunctor _ (ComplexShape.down ℕ)).map f.op
  have hm : homologyMap (dualMap f) n ≫ ((K.op.sc n).mapHomologyIso dualFunctor).hom =
      ((L.op.sc n).mapHomologyIso dualFunctor).hom ≫ dualFunctor.map (homologyMap fo n) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor _ (ComplexShape.up ℕ) n).map fo) dualFunctor
  change homologyMap (dualMap f) n ≫
      (((K.op.sc n).mapHomologyIso dualFunctor).hom ≫ dualFunctor.map (K.homologyOp n).hom) =
    (((L.op.sc n).mapHomologyIso dualFunctor).hom ≫ dualFunctor.map (L.homologyOp n).hom) ≫
      dualFunctor.map (homologyMap f n).op
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ dualFunctor.map (K.homologyOp n).hom) hm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun t => ((L.op.sc n).mapHomologyIso dualFunctor).hom ≫ t)
    (dualFunctor.map_comp _ _).symm) ?_
  refine Eq.trans (congrArg
    (fun t => ((L.op.sc n).mapHomologyIso dualFunctor).hom ≫ dualFunctor.map t)
    (homologyOp_hom_naturality f n)) ?_
  refine Eq.trans (congrArg
    (fun t => ((L.op.sc n).mapHomologyIso dualFunctor).hom ≫ t)
    (dualFunctor.map_comp _ _)) ?_
  exact (Category.assoc _ _ _).symm

end TernaryPoly.RationalHomologyDual
