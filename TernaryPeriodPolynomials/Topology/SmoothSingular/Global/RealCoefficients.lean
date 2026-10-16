module

/- Explicit real-scalar adaptation of the complex coefficient splitting. -/
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
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
open CategoryTheory TensorProduct
namespace TernaryPoly.SmoothSingularGlobal

/-- The actual exact restriction-of-scalars functor from real to rational modules. -/
abbrev forgetReal : ModuleCat ℝ ⥤ ModuleCat ℚ :=
  ModuleCat.restrictScalars (algebraMap ℚ ℝ)

variable {G : Type} [Group G]

/-- Restrict the coefficient scalars of an actual real representation. -/
def rationalAction (B : Rep.{0} ℝ G) :
    Representation ℚ G (forgetReal.obj (ModuleCat.of ℝ B)) where
  toFun g := (forgetReal.map (ModuleCat.ofHom (B.ρ g))).hom
  map_one' := by
    apply LinearMap.ext
    intro x
    change B.ρ 1 x=x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change B.ρ (g*h) x=B.ρ g (B.ρ h x)
    rw [map_mul]
    rfl

abbrev rationalRep (B : Rep.{0} ℝ G) : Rep ℚ G := Rep.of (rationalAction B)

/-- Genuine real scalar extension on ℝ tensor_ℚ A. -/
def realAction (A : Rep.{0} ℚ G) : Representation ℝ G (ℝ ⊗[ℚ] A) :=
  (Module.End.baseChangeHom ℚ ℝ A).toMonoidHom.comp A.ρ

abbrev realRep (A : Rep.{0} ℚ G) : Rep ℝ G := Rep.of (realAction A)

@[simp] theorem realAction_tmul (A : Rep.{0} ℚ G) (g : G) (z : ℝ) (x : A) :
    realAction A g (z ⊗ₜ[ℚ] x)=z ⊗ₜ[ℚ] A.ρ g x := rfl

/-- A rational linear functional on ℝ normalized at 1, requiring no finite-dimensionality. -/
def rationalFunctional : ℝ →ₗ[ℚ] ℚ :=
  Classical.choose (Module.Projective.exists_dual_eq_one ℚ (by norm_num : (1 : ℝ)≠0))

@[simp] theorem rationalFunctional_one : rationalFunctional 1=1 :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one ℚ (by norm_num : (1 : ℝ)≠0))

/-- The actual coefficient inclusion x ↦ 1 tensor x. -/
def coefficientInclusion (A : Rep.{0} ℚ G) : A ⟶ rationalRep (realRep A) :=
  Rep.ofHom ⟨{
    toFun x := 1 ⊗ₜ[ℚ] x
    map_add' x y := TensorProduct.tmul_add 1 x y
    map_smul' q x := by
      change (1 : ℝ) ⊗ₜ[ℚ] (q • x)=(algebraMap ℚ ℝ q) • ((1 : ℝ) ⊗ₜ[ℚ] x)
      rw [IsScalarTower.algebraMap_smul,TensorProduct.tmul_smul]},by
    intro g
    apply LinearMap.ext
    intro x
    rfl⟩

/-- The rational tensor retraction induced by the fixed functional ℝ→ℚ. -/
def tensorRetraction (A : Rep.{0} ℚ G) : ℝ ⊗[ℚ] A →ₗ[ℚ] A :=
  (TensorProduct.lid ℚ A).toLinearMap.comp (TensorProduct.map rationalFunctional LinearMap.id)

@[simp] theorem tensorRetraction_tmul (A : Rep.{0} ℚ G) (z : ℝ) (x : A) :
    tensorRetraction A (z ⊗ₜ[ℚ] x)=rationalFunctional z • x := by
  simp [tensorRetraction]

/-- The retraction is equivariant for the actual rational restriction of real coefficients. -/
def coefficientRetraction (A : Rep.{0} ℚ G) : rationalRep (realRep A) ⟶ A :=
  Rep.ofHom ⟨{
    toFun := tensorRetraction A
    map_add' := (tensorRetraction A).map_add
    map_smul' q x := by
      change ℝ ⊗[ℚ] A at x
      change tensorRetraction A ((algebraMap ℚ ℝ q) • x)=q • tensorRetraction A x
      rw [IsScalarTower.algebraMap_smul, map_smul]},by
    intro g
    apply LinearMap.ext
    intro x
    change ℝ ⊗[ℚ] A at x
    change tensorRetraction A (realAction A g x)=A.ρ g (tensorRetraction A x)
    induction x using TensorProduct.inductionOn with
    | tmul z x => rw [realAction_tmul,tensorRetraction_tmul,tensorRetraction_tmul,map_smul]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (·+·) hx hy⟩

/-- The coefficient inclusion is genuinely split, without a group or dimension restriction. -/
theorem coefficient_split (A : Rep.{0} ℚ G) :
    coefficientInclusion A ≫ coefficientRetraction A=𝟙 A := by
  ext x
  change tensorRetraction A (1 ⊗ₜ[ℚ] x)=x
  rw [tensorRetraction_tmul,rationalFunctional_one,one_smul]

end TernaryPoly.SmoothSingularGlobal
