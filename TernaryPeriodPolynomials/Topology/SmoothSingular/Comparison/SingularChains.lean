module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.Hom
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Order.Fin.InsertNth
public import Mathlib.Order.Fin.Prod
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial

/-- The actual Mathlib real singular chains, with the real coefficient-one generator. -/
abbrev realSingularChains (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℝ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ)).obj X

/-- Continuous maps act on the actual real singular chains. -/
abbrev realSingularChainMap {X Y : TopCat.{0}} (f : X ⟶ Y) :
    realSingularChains X ⟶ realSingularChains Y :=
  ((singularChainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ)).map f

/-- A genuine continuous homotopy equivalence induces a real singular chain homotopy equivalence. -/
def realSingularChainHomotopyEquiv {X Y : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv (realSingularChains X) (realSingularChains Y) where
  hom := realSingularChainMap (TopCat.ofHom e.toFun)
  inv := realSingularChainMap (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    rw [← Functor.map_comp]
    have H : TopCat.Homotopy ((TopCat.ofHom e.toFun) ≫ (TopCat.ofHom e.invFun)) (𝟙 X) := e.left_inv.some
    exact (H.singularChainComplexFunctorObjMap (ModuleCat.of ℝ ℝ)).trans
      (_root_.Homotopy.ofEq (((singularChainComplexFunctor (ModuleCat ℝ)).obj
        (ModuleCat.of ℝ ℝ)).map_id _))
  homotopyInvHomId := by
    rw [← Functor.map_comp]
    have H : TopCat.Homotopy ((TopCat.ofHom e.invFun) ≫ (TopCat.ofHom e.toFun)) (𝟙 Y) := e.right_inv.some
    exact (H.singularChainComplexFunctorObjMap (ModuleCat.of ℝ ℝ)).trans
      (_root_.Homotopy.ofEq (((singularChainComplexFunctor (ModuleCat ℝ)).obj
        (ModuleCat.of ℝ ℝ)).map_id _))

/-- Real singular chains are exact in every positive degree on a contractible space. -/
theorem realSingularChains_exactAt (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) :
    (realSingularChains X).ExactAt (n+1) := by
  apply (exactAt_iff_isZero_homology _ _).mpr
  let e := realSingularChainHomotopyEquiv (Y := TopCat.of Unit) (ContractibleSpace.hequiv_unit X).some
  have hU : IsZero ((realSingularChains (TopCat.of Unit)).homology (n+1)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat ℝ) (n+1)
      (ModuleCat.of ℝ ℝ) (TopCat.of Unit) (Nat.succ_ne_zero n)
  exact hU.of_iso (e.toHomologyIso (n+1))

/-- The canonical map from zero chains to their actual homology classes. -/
def realZeroClass (K : ChainComplex (ModuleCat ℝ) ℕ) : K.X 0 ⟶ K.homology 0 :=
  K.liftCycles (𝟙 (K.X 0)) 0 (by simp) (by simp) ≫ K.homologyπ 0

/-- The canonical zero-class map retains the actual opcycle quotient. -/
theorem realZeroClass_opcycles (K : ChainComplex (ModuleCat ℝ) ℕ) :
    realZeroClass K ≫ K.homologyι 0 = K.pOpcycles 0 := by
  unfold realZeroClass
  rw [Category.assoc, homology_π_ι, ← Category.assoc, liftCycles_i, Category.id_comp]

/-- Degree-zero class formation is natural for the genuine chain maps. -/
theorem realZeroClass_natural {K L : ChainComplex (ModuleCat ℝ) ℕ} (f : K ⟶ L) :
    realZeroClass K ≫ homologyMap f 0 = f.f 0 ≫ realZeroClass L := by
  apply (cancel_mono (L.homologyι 0)).mp
  rw [Category.assoc, homologyι_naturality, ← Category.assoc, realZeroClass_opcycles,
    Category.assoc, realZeroClass_opcycles, p_opcyclesMap]

/-- A zero-chain has zero homology class exactly when it is an actual boundary. -/
theorem realZeroClass_eq_zero (K : ChainComplex (ModuleCat ℝ) ℕ) (x : K.X 0) :
    realZeroClass K x = 0 ↔ x ∈ LinearMap.range (K.d 1 0).hom := by
  have h := (K.sc 0).moduleCat_pOpcycles_eq_zero_iff x
  have hr : LinearMap.range (K.sc 0).f.hom = LinearMap.range (K.d 1 0).hom :=
    congrArg (fun i : ℕ => LinearMap.range (K.d i 0).hom) (ChainComplex.prev ℕ 0)
  rw [hr] at h
  constructor
  · intro hx
    apply h.mp
    have hx' := congrArg (fun y => K.homologyι 0 y) hx
    rw [map_zero] at hx'
    change (realZeroClass K ≫ K.homologyι 0) x = 0 at hx'
    rw [realZeroClass_opcycles] at hx'
    exact hx'
  · intro hx
    apply (ModuleCat.mono_iff_injective (K.homologyι 0)).mp inferInstance
    have hx' := h.mpr hx
    change (realZeroClass K ≫ K.homologyι 0) x = K.homologyι 0 0
    rw [realZeroClass_opcycles, map_zero]
    exact hx'

end TernaryPoly.SmoothSingularComparison
