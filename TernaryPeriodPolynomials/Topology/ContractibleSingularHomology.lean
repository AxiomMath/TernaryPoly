module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne
public import Mathlib.CategoryTheory.Limits.MonoCoprod
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
public import Mathlib.Order.Fin.InsertNth
public import Mathlib.Order.Fin.Prod
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.ContractibleSingularHomology
open CategoryTheory Limits AlgebraicTopology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual Mathlib singular rational chain complex. -/
abbrev chains (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of.{0} ℚ ℚ)).obj (TopCat.of X)

/-- A genuine topological homotopy equivalence induces a genuine chain homotopy equivalence. -/
def chainHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv (chains X) (chains Y) where
  hom := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of.{0} ℚ ℚ)).map
    (TopCat.ofHom e.toFun)
  inv := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of.{0} ℚ ℚ)).map
    (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    rw [←Functor.map_comp]
    have H : TopCat.Homotopy ((TopCat.ofHom e.toFun) ≫ (TopCat.ofHom e.invFun))
        (𝟙 (TopCat.of X)) := e.left_inv.some
    exact (H.singularChainComplexFunctorObjMap (ModuleCat.of.{0} ℚ ℚ)).trans
      (_root_.Homotopy.ofEq (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of.{0} ℚ ℚ)).map_id _))
  homotopyInvHomId := by
    rw [←Functor.map_comp]
    have H : TopCat.Homotopy ((TopCat.ofHom e.invFun) ≫ (TopCat.ofHom e.toFun))
        (𝟙 (TopCat.of Y)) := e.right_inv.some
    exact (H.singularChainComplexFunctorObjMap (ModuleCat.of.{0} ℚ ℚ)).trans
      (_root_.Homotopy.ofEq (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of.{0} ℚ ℚ)).map_id _))

/-- Positive-degree singular homology of every contractible space is zero. -/
theorem homology_isZero [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero ((chains X).homology n) := by
  let e := chainHomotopyEquiv (ContractibleSpace.hequiv_unit X).some
  have hU : IsZero ((chains Unit).homology n) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{0} ℚ) n
      (ModuleCat.of.{0} ℚ ℚ) (TopCat.of Unit) hn
  exact hU.of_iso (e.toHomologyIso n)

/-- The exact Mathlib singular chain complex is exact in every positive degree. -/
theorem chains_exactAt [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (chains X).ExactAt n :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (homology_isZero (X := X) n hn)

/-- The degree-zero augmentation induces an isomorphism with the literal coefficient module. -/
def homologyZeroIso [ContractibleSpace X] :
    (chains X).homology 0 ≅ ModuleCat.of.{0} ℚ ℚ := by
  letI : PathConnectedSpace (TopCat.of X) := inferInstanceAs (PathConnectedSpace X)
  exact @asIso (ModuleCat.{0} ℚ) _ _ _
    ((TopCat.of X).singularHomology₀ε (ModuleCat.of.{0} ℚ ℚ))
    (TopCat.instIsIsoSingularHomology₀εOfPathConnectedSpaceCarrier
      (TopCat.of X) (ModuleCat.of.{0} ℚ ℚ))

end TernaryPoly.ContractibleSingularHomology
