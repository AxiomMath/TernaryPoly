module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LeviCrossedAction
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Order.Fin.SuccAboveOrderIso

@[expose] public section


/-!
# Mathlib `H¹` versus the crossed-homomorphism model

For a representation `A : Rep ℂ G`, Mathlib's `groupCohomology.H1 A` and the library's
`CrossedH1 A.ρ = crossedCocycles / crossedBoundaries` are isomorphic (`h1EquivCrossed`), by the
identity on cochains: the cocycle conditions agree, and `H1π x = 0` iff `x` is a coboundary.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous CategoryTheory
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic

variable {G : Type} [Group G] (A : Rep ℂ G)

/-- A Mathlib one-cocycle is a crossed homomorphism. -/
def crossedOfCocycle : groupCohomology.cocycles₁ A →ₗ[ℂ] crossedCocycles A.ρ where
  toFun f := ⟨⇑f, fun g h =>
    ((groupCohomology.mem_cocycles₁_iff (A := A) f.1).mp f.2 g h).trans (add_comm _ _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A crossed homomorphism is a Mathlib one-cocycle. -/
def cocycleOfCrossed : crossedCocycles A.ρ →ₗ[ℂ] groupCohomology.cocycles₁ A where
  toFun f := ⟨f.val, (groupCohomology.mem_cocycles₁_iff (A := A) f.val).mpr fun g h => by
    rw [f.property g h, add_comm]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem crossedOfCocycle_cocycleOfCrossed (f : crossedCocycles A.ρ) :
    crossedOfCocycle A (cocycleOfCrossed A f) = f := rfl

theorem cocycleOfCrossed_crossedOfCocycle (f : groupCohomology.cocycles₁ A) :
    cocycleOfCrossed A (crossedOfCocycle A f) = f := rfl

theorem coboundary_iff (f : crossedCocycles A.ρ) :
    ⇑(cocycleOfCrossed A f) ∈ groupCohomology.coboundaries₁ A ↔
      f ∈ crossedBoundaries A.ρ := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, Subtype.ext (funext fun g => ?_)⟩
    have := congrFun ha g
    rw [groupCohomology.d₀₁_hom_apply] at this
    exact this
  · rintro ⟨a, ha⟩
    refine ⟨a, funext fun g => ?_⟩
    rw [groupCohomology.d₀₁_hom_apply]
    exact congrArg (fun y : crossedCocycles A.ρ => y.val g) ha

/-- The comparison map from the crossed model to Mathlib's `H¹`. -/
def crossedToH1 : CrossedH1 A.ρ →ₗ[ℂ] groupCohomology.H1 A :=
  (crossedBoundaries A.ρ).liftQ ((groupCohomology.H1π A).hom ∘ₗ cocycleOfCrossed A) (by
    rintro f ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    change (groupCohomology.H1π A) (cocycleOfCrossed A (crossedBoundary A.ρ a)) = 0
    rw [groupCohomology.H1π_eq_zero_iff]
    exact (coboundary_iff A _).mpr ⟨a, rfl⟩)

theorem crossedToH1_bijective : Function.Bijective (crossedToH1 A) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨f, rfl⟩ := (crossedBoundaries A.ρ).mkQ_surjective m
    have h : (groupCohomology.H1π A) (cocycleOfCrossed A f) = 0 := hm
    rw [groupCohomology.H1π_eq_zero_iff] at h
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((coboundary_iff A f).mp h)
  · intro c
    induction c using groupCohomology.H1_induction_on with
    | h x => exact ⟨(crossedBoundaries A.ρ).mkQ (crossedOfCocycle A x), rfl⟩

/-- **Mathlib's `H¹` is the crossed-homomorphism model.** -/
def h1EquivCrossed : CrossedH1 A.ρ ≃ₗ[ℂ] groupCohomology.H1 A :=
  LinearEquiv.ofBijective (crossedToH1 A) (crossedToH1_bijective A)

theorem h1EquivCrossed_mk (f : crossedCocycles A.ρ) :
    h1EquivCrossed A ((crossedBoundaries A.ρ).mkQ f) =
      (groupCohomology.H1π A) (cocycleOfCrossed A f) := rfl

end TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
