module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Binary.LeviReduction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

section Pullback

variable {Source Target Value : Type} [Group Source] [Group Target]
  [AddCommGroup Value] [Module ℂ Value]
  (homomorphism : Source →* Target) (representation : Representation ℂ Target Value)

def crossedPullbackCocycles :
    crossedCocycles representation →ₗ[ℂ] crossedCocycles (representation.comp homomorphism) where
  toFun cochain := ⟨fun element => cochain.val (homomorphism element), by
    intro first second
    change cochain.val (homomorphism (first * second)) = cochain.val (homomorphism first) +
      representation (homomorphism first) (cochain.val (homomorphism second))
    rw [map_mul]
    exact cochain.property (homomorphism first) (homomorphism second)⟩
  map_add' first second := rfl
  map_smul' scalar cochain := rfl

theorem crossedPullbackCocycles_boundary (value : Value) :
    crossedPullbackCocycles homomorphism representation (crossedBoundary representation value) =
      crossedBoundary (representation.comp homomorphism) value := by
  apply Subtype.ext
  rfl

def crossedPullbackH1 :
    CrossedH1 representation →ₗ[ℂ] CrossedH1 (representation.comp homomorphism) :=
  (crossedBoundaries representation).mapQ (crossedBoundaries (representation.comp homomorphism))
    (crossedPullbackCocycles homomorphism representation) (by
      rintro cochain ⟨value, rfl⟩
      exact ⟨value, (crossedPullbackCocycles_boundary homomorphism representation value).symm⟩)

theorem crossedPullbackH1_mk (cochain : crossedCocycles representation) :
    crossedPullbackH1 homomorphism representation ((crossedBoundaries representation).mkQ cochain) =
      (crossedBoundaries (representation.comp homomorphism)).mkQ
        (crossedPullbackCocycles homomorphism representation cochain) := rfl

end Pullback

variable {Radical Levi Smaller Value : Type} [Group Radical] [Group Levi] [Group Smaller]
  [AddCommGroup Value] [Module ℂ Value]
  (action : Levi →* MulAut Radical)
  (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)
  (homomorphism : Smaller →* Levi)

theorem mixedRestriction_zero_of_boundary
    (cycle : radicalZeroTwoCycles action representation)
    (primitive : SemidirectProduct Radical Levi action → Value)
    (radicalZero : inhomogeneousBoundaryMap representation primitive ∈
      radicalZeroTwoCycles action representation)
    (leftBoundary : ∀ element radical,
      cycle.val.val (SemidirectProduct.inr (homomorphism element)) (SemidirectProduct.inl radical) =
        (inhomogeneousBoundaryMap representation primitive).val
          (SemidirectProduct.inr (homomorphism element)) (SemidirectProduct.inl radical))
    (rightBoundary : ∀ radical element,
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr (homomorphism element)) =
        (inhomogeneousBoundaryMap representation primitive).val
          (SemidirectProduct.inl radical) (SemidirectProduct.inr (homomorphism element))) :
    crossedPullbackH1 homomorphism (leviCrossedH1Representation action representation)
      (mixedClassMap action representation cycle) = 0 := by
  let boundaryCycle : radicalZeroTwoCycles action representation :=
    ⟨inhomogeneousBoundaryMap representation primitive, radicalZero⟩
  have same : crossedPullbackCocycles homomorphism (leviCrossedH1Representation action representation)
      (mixedH1CocycleMap action representation cycle) =
    crossedPullbackCocycles homomorphism (leviCrossedH1Representation action representation)
      (mixedH1CocycleMap action representation boundaryCycle) := by
    apply Subtype.ext
    funext element
    change (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
      (mixedCrossedMap action representation (homomorphism element) cycle) =
      (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
        (mixedCrossedMap action representation (homomorphism element) boundaryCycle)
    apply congrArg
    apply Subtype.ext
    funext radical
    change cycle.val.val (SemidirectProduct.inr (homomorphism element))
        (SemidirectProduct.inl (action (homomorphism element)⁻¹ radical)) -
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr (homomorphism element)) = _
    rw [leftBoundary, rightBoundary]
    rfl
  change (crossedBoundaries ((leviCrossedH1Representation action representation).comp homomorphism)).mkQ
    (crossedPullbackCocycles homomorphism (leviCrossedH1Representation action representation)
      (mixedH1CocycleMap action representation cycle)) = 0
  rw [same]
  change (crossedBoundaries ((leviCrossedH1Representation action representation).comp homomorphism)).mkQ
    (crossedPullbackCocycles homomorphism (leviCrossedH1Representation action representation)
      (mixedH1CocycleMap action representation
        ⟨inhomogeneousBoundaryMap representation primitive, radicalZero⟩)) = 0
  rw [mixedH1CocycleMap_boundary, crossedPullbackCocycles_boundary]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩

theorem mixedRestriction_zero_of_subgroup_boundary
    (cycle : radicalZeroTwoCycles action representation)
    (subgroup : Subgroup (SemidirectProduct Radical Levi action))
    (radicalMem : ∀ radical, SemidirectProduct.inl radical ∈ subgroup)
    (leviMem : ∀ element, SemidirectProduct.inr (homomorphism element) ∈ subgroup)
    (primitive : SemidirectProduct Radical Levi action → Value)
    (boundary : ∀ first ∈ subgroup, ∀ second ∈ subgroup,
      (inhomogeneousBoundaryMap representation primitive).val first second = cycle.val.val first second) :
    crossedPullbackH1 homomorphism (leviCrossedH1Representation action representation)
      (mixedClassMap action representation cycle) = 0 := by
  apply mixedRestriction_zero_of_boundary action representation homomorphism cycle primitive
  · intro first second
    rw [boundary _ (radicalMem first) _ (radicalMem second)]
    exact cycle.property first second
  · intro element radical
    exact (boundary _ (leviMem element) _ (radicalMem radical)).symm
  · intro radical element
    exact (boundary _ (radicalMem radical) _ (leviMem element)).symm

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
