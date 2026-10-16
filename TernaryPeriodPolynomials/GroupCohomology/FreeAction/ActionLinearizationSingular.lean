module

public import TernaryPeriodPolynomials.GroupCohomology.FreeAction.ActionLinearizationRepresentation
public import TernaryPeriodPolynomials.GroupCohomology.FreeAction.ActionLinearizationContinuous
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.Order.Fin.SuccAboveOrderIso

@[expose] public section

noncomputable section
namespace TernaryPoly.FreeActionLinearization
open CategoryTheory
open scoped Simplicial

universe u v w

/-- The literal Mathlib singular-simplex type used by singularChainComplexFunctor. -/
abbrev SingularSimplex (X : TopCat.{w}) (n : ℕ) :=
  (TopCat.toSSet.obj X).obj (.op ⦋n⦌)

section Action
variable (G : Type v) (X : TopCat.{w}) [Group G]
variable [MulAction G X] [ContinuousConstSMul G X]

/-- The action transported through Mathlib's exact singular-simplex equivalence. -/
instance singularMulAction (n : ℕ) : MulAction G (SingularSimplex X n) :=
  (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).mulAction G

/-- The actual singular-simplex equivalence is equivariant for pointwise scalar multiplication. -/
@[simp] theorem singularEquiv_smul (n : ℕ) (g : G) (σ : SingularSimplex X n) :
    TopCat.toSSetObjEquiv X (.op ⦋n⦌) (g • σ) =
      g • TopCat.toSSetObjEquiv X (.op ⦋n⦌) σ := by
  exact (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).apply_symm_apply _

/-- The actual scalar action as a continuous self-map of the given topological space. -/
def scalarMap (g : G) : X ⟶ X :=
  TopCat.ofHom ⟨fun x => g • x,continuous_const_smul g⟩

/-- The transported action is exactly the map of Mathlib's singular-set functor. -/
theorem singular_smul_eq_map (n : ℕ) (g : G) (σ : SingularSimplex X n) :
    g • σ = (TopCat.toSSet.map (scalarMap G X g)).app (.op ⦋n⦌) σ := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
  rw [singularEquiv_smul]
  rfl

variable [IsCancelSMul G X]

/-- A singular simplex has nonempty domain, so freeness is detected by evaluation. -/
instance singular_isCancelSMul (n : ℕ) : IsCancelSMul G (SingularSimplex X n) where
  right_cancel' g h σ heq := by
    apply continuousMap_smul_right_cancel G _ X g h
      (TopCat.toSSetObjEquiv X (.op ⦋n⦌) σ)
    simpa only [singularEquiv_smul] using
      congrArg (TopCat.toSSetObjEquiv X (.op ⦋n⦌)) heq

end Action

section Representation
variable (k : Type u) (G : Type v) (X : TopCat.{max u v w})
variable [CommRing k] [Group G] [MulAction G X] [ContinuousConstSMul G X] [IsCancelSMul G X]

/-- An explicit free representation on the actual singular-simplex orbits in every degree. -/
def singularPermutationIsoFree (n : ℕ) :
    Rep.ofMulAction k G (SingularSimplex X n) ≅
      Rep.free k G (Orbits G (SingularSimplex X n)) :=
  permutationIsoFree k G (SingularSimplex X n)

/-- Projectivity of the actual degree-n singular-simplex permutation representation. -/
instance singular_permutation_projective (n : ℕ) :
    Projective (Rep.ofMulAction k G (SingularSimplex X n)) :=
  permutation_projective k G (SingularSimplex X n)

end Representation
end TernaryPoly.FreeActionLinearization
