module

public import TernaryPeriodPolynomials.Building.Integer.TopInjective
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section


open CategoryTheory

noncomputable section
namespace TernaryPoly.LatticeTopCohomology
open IntegerGridExactness

abbrev Lattice := Multiplicative (ℤ × ℤ)
abbrev P₀ := Rep.leftRegular ℚ Lattice
abbrev P₁ := Rep.free ℚ Lattice (Fin 2)
abbrev P₂ := P₀
abbrev Trivial := Rep.trivial ℚ Lattice ℚ

def first : Lattice := Multiplicative.ofAdd (1,0)
def second : Lattice := Multiplicative.ofAdd (0,1)

def latticeEquiv : Lattice ≃ Vertex where
  toFun := Multiplicative.toAdd
  invFun := Multiplicative.ofAdd
  left_inv _ := rfl
  right_inv _ := rfl

/-- Concrete finite grid coordinates for the regular representation. -/
def grid₀ : P₀ ≃ₗ[ℚ] C₀ :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).trans (Finsupp.domLCongr latticeEquiv)

/-- Concrete finite grid coordinates for the rank-two free representation. -/
def grid₁ : P₁ ≃ₗ[ℚ] C₁ :=
  (Finsupp.mapRange.linearEquiv grid₀).trans
    ((Finsupp.curryLinearEquiv ℚ).symm.trans (Finsupp.domLCongr (Equiv.prodComm _ _)))

@[simp] theorem grid₀_single (g : Lattice) (r : ℚ) :
    grid₀ (MonoidAlgebra.single g r) = Finsupp.single g.toAdd r := by
  simp [grid₀, latticeEquiv]

@[simp] theorem grid₁_single (i : Fin 2) (g : Lattice) (r : ℚ) :
    grid₁ (Finsupp.single i (MonoidAlgebra.single g r)) = Finsupp.single (g.toAdd,i) r := by
  simp [grid₁, Finsupp.mapRange.linearEquiv_apply, grid₀, latticeEquiv]

/-- The two endpoint-minus-start generators, as an actual representation morphism. -/
def d₁ : P₁ ⟶ P₀ :=
  Rep.freeLift ℚ Lattice P₀ ![MonoidAlgebra.single first 1 - MonoidAlgebra.single 1 1,
    MonoidAlgebra.single second 1 - MonoidAlgebra.single 1 1]

/-- The positively oriented square boundary in the free edge module. -/
def topBoundary : P₁ :=
  Finsupp.single 0 (MonoidAlgebra.single 1 1) +
    Finsupp.single 1 (MonoidAlgebra.single first 1) -
    Finsupp.single 0 (MonoidAlgebra.single second 1) -
    Finsupp.single 1 (MonoidAlgebra.single 1 1)

def d₂ : P₂ ⟶ P₁ := Rep.leftRegularHom P₁ topBoundary

def augmentationHom : P₀ ⟶ Trivial := Rep.leftRegularHom Trivial 1

@[simp] theorem d₁_single (i : Fin 2) (g : Lattice) (r : ℚ) :
    d₁.hom (Finsupp.single i (MonoidAlgebra.single g r)) =
      r • (MonoidAlgebra.single (g * (![first,second] i)) 1 - MonoidAlgebra.single g 1) := by
  simp only [d₁, Rep.freeLift]
  fin_cases i <;> simp [Representation.ofMulAction_single]

@[simp] theorem d₂_single (g : Lattice) (r : ℚ) :
    d₂.hom (MonoidAlgebra.single g r) = r •
      (Finsupp.single 0 (MonoidAlgebra.single g 1) +
        Finsupp.single 1 (MonoidAlgebra.single (g*first) 1) -
        Finsupp.single 0 (MonoidAlgebra.single (g*second) 1) -
        Finsupp.single 1 (MonoidAlgebra.single g 1)) := by
  simp [d₂, topBoundary, Representation.finsupp_single,
    Representation.ofMulAction_single]

@[simp] theorem augmentationHom_single (g : Lattice) (r : ℚ) :
    augmentationHom.hom (MonoidAlgebra.single g r) = r := by
  simp [augmentationHom]

/-- The free-module first differential is exactly the infinite-grid boundary. -/
theorem grid_d₁ (z : P₁) : grid₀ (d₁.hom z) = boundary₁ (grid₁ z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single i a =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp only [Finsupp.single_zero, map_zero]
    | add x y hx hy => simp only [Finsupp.single_add, map_add, hx, hy]
    | single g r =>
      rw [d₁_single, map_smul, map_sub, grid₀_single, grid₀_single, grid₁_single,
        boundary₁_single]
      congr 1
      fin_cases i <;> simp [first, second, vertex, edgeHead, Prod.add_def]

/-- The free-module second differential is exactly the square boundary. -/
theorem grid_d₂ (z : P₂) : grid₁ (d₂.hom z) = boundary₂ (grid₀ z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g r =>
    rw [d₂_single, map_smul, map_sub, map_sub, map_add,
      grid₁_single, grid₁_single, grid₁_single, grid₁_single,
      grid₀_single, boundary₂_single]
    simp [squareBoundary, horizontal, vertical, first, second, Prod.add_def]

theorem grid_augmentation (z : P₀) : augmentationHom.hom z = augmentation (grid₀ z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g r => rw [augmentationHom_single, grid₀_single, augmentation_single]

/-- The actual equivariant differentials square to zero. -/
theorem d₂_d₁ : d₂ ≫ d₁ = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  apply grid₀.injective
  change grid₀ (d₁.hom (d₂.hom z)) = grid₀ 0
  rw [grid_d₁, grid_d₂, boundary₁_boundary₂, map_zero]

theorem d₁_augmentation : d₁ ≫ augmentationHom = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change augmentationHom.hom (d₁.hom z) = 0
  rw [grid_augmentation, grid_d₁, augmentation_boundary₁]

end TernaryPoly.LatticeTopCohomology
