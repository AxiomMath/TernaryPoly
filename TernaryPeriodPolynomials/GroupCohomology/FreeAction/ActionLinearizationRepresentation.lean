module

public import TernaryPeriodPolynomials.GroupCohomology.FreeAction.ActionLinearization
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.Data.Fintype.Order
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section

noncomputable section
namespace TernaryPoly.FreeActionLinearization
open CategoryTheory
open scoped MonoidAlgebra

universe u v w
variable (k : Type u) (G : Type v) (X : Type (max u v w))
variable [CommRing k] [Group G] [MulAction G X] [IsCancelSMul G X]

/-- Actual group-algebra coefficients, uncurrying, and the literal orbit parametrization. -/
def freePermutationLinearEquiv : (Orbits G X →₀ k[G]) ≃ₗ[k] k[X] :=
  Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k) ≪≫ₗ
    (Finsupp.curryLinearEquiv k).symm ≪≫ₗ
    Finsupp.domLCongr (orbitProductEquiv G X) ≪≫ₗ
    (MonoidAlgebra.coeffLinearEquiv k).symm

/-- A basis vector indexed by an orbit and a group element goes to the actual orbit point. -/
@[simp] theorem freePermutationLinearEquiv_single (q : Orbits G X) (g : G) (r : k) :
    freePermutationLinearEquiv k G X (Finsupp.single q (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • q.out) r := by
  simp [freePermutationLinearEquiv]

/-- The coefficient equivalence intertwines the actual regular and permutation actions. -/
def freePermutationEquiv :
    (Representation.free k G (Orbits G X)).Equiv (Representation.ofMulAction k G X) :=
  .mk (freePermutationLinearEquiv k G X) fun g => by
    ext q h r
    simp [mul_smul]

/-- The actual permutation representation is explicitly free on the set of its orbits. -/
def permutationIsoFree : Rep.ofMulAction k G X ≅ Rep.free k G (Orbits G X) :=
  (Rep.mkIso (freePermutationEquiv k G X)).symm

/-- The inverse isomorphism sends the literal free basis to the chosen orbit representatives. -/
@[simp] theorem permutationIsoFree_inv_single (q : Orbits G X) (g : G) (r : k) :
    (permutationIsoFree k G X).inv.hom (Finsupp.single q (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • q.out) r := by
  exact freePermutationLinearEquiv_single k G X q g r

/-- No finiteness or stabilizer-order hypothesis is needed for a free permutation representation. -/
instance permutation_projective : Projective (Rep.ofMulAction k G X) :=
  Projective.of_iso (permutationIsoFree k G X).symm
    (Rep.free_projective.{max v w,u,v} (k := k) (G := G) (α := Orbits G X))

end TernaryPoly.FreeActionLinearization
