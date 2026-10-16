module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CochainCoordinates

@[expose] public section


open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

def splitInvariantAction {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (levi : L) :
    Module.End ℂ (Rep.res extension.inl representation).ρ.invariants :=
  ((representation.ρ (splitting levi)).comp (Rep.res extension.inl representation).ρ.invariants.subtype).codRestrict _ (by
    intro vector
    apply (Representation.mem_invariants _ _).mpr
    intro radical
    change representation.ρ (extension.inl radical) (representation.ρ (splitting levi) vector.val) =
      representation.ρ (splitting levi) vector.val
    have invariant := (Representation.mem_invariants _ _).mp vector.property
      (splitRadicalInput splitting levi radical)
    change representation.ρ (extension.inl (splitRadicalInput splitting levi radical)) vector.val = vector.val at invariant
    rw [← Module.End.mul_apply, ← map_mul, splitRadicalInput_commute, map_mul, Module.End.mul_apply, invariant])

theorem splitInvariantAction_apply {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (levi : L) (vector : (Rep.res extension.inl representation).ρ.invariants) :
    (splitInvariantAction splitting representation levi vector).val = representation.ρ (splitting levi) vector.val := rfl

def splitInvariantRepresentation {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) : Rep ℂ L :=
  Rep.of {
    toFun := splitInvariantAction splitting representation
    map_one' := by
      apply LinearMap.ext
      intro vector
      apply Subtype.ext
      change representation.ρ (splitting 1) vector.val = vector.val
      rw [map_one, map_one, Module.End.one_apply]
    map_mul' first second := by
      apply LinearMap.ext
      intro vector
      apply Subtype.ext
      change representation.ρ (splitting (first * second)) vector.val =
        representation.ρ (splitting first) (representation.ρ (splitting second) vector.val)
      rw [map_mul, map_mul, Module.End.mul_apply] }

theorem splitInvariant_full_action {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (element : E) (vector : (Rep.res extension.inl representation).ρ.invariants) :
    representation.ρ element vector.val =
      ((splitInvariantRepresentation splitting representation).ρ (extension.rightHom element) vector).val := by
  obtain ⟨radical, levi, rfl⟩ := split_exists_pair splitting element
  change representation.ρ (extension.inl radical * splitting levi) vector.val =
    (splitInvariantAction splitting representation
      (extension.rightHom (extension.inl radical * splitting levi)) vector).val
  rw [extension.rightHom.map_mul, extension.rightHom_inl, splitting.rightHom_splitting, one_mul]
  rw [map_mul, Module.End.mul_apply]
  exact (Representation.mem_invariants _ _).mp (splitInvariantAction splitting representation levi vector).property radical

def splitInvariantInclusion {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) :
    Rep.res extension.rightHom (splitInvariantRepresentation splitting representation) ⟶ representation :=
  Rep.ofHom ⟨(Rep.res extension.inl representation).ρ.invariants.subtype, by
    intro element
    apply LinearMap.ext
    intro vector
    exact (splitInvariant_full_action splitting representation element vector).symm⟩

/-- Inflation from Levi cohomology with radical-invariant coefficients. -/
def splitInvariantInflation {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) :
    groupCohomology.H2 (splitInvariantRepresentation splitting representation) →ₗ[ℂ]
      groupCohomology.H2 representation :=
  (groupCohomology.map extension.rightHom (splitInvariantInclusion splitting representation) 2).hom

def splitInflatedCocycle {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) :
    groupCohomology.cocycles₂ (splitInvariantRepresentation splitting representation) →ₗ[ℂ]
      groupCohomology.cocycles₂ representation :=
  (groupCohomology.mapCocycles₂ extension.rightHom (splitInvariantInclusion splitting representation)).hom

theorem splitInflatedCocycle_apply {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ (splitInvariantRepresentation splitting representation))
    (first second : E) :
    splitInflatedCocycle splitting representation cycle (first, second) =
      (cycle (extension.rightHom first, extension.rightHom second)).val := by
  exact congrFun (groupCohomology.mapCocycles₂_comp_i_apply extension.rightHom
    (splitInvariantInclusion splitting representation) cycle) (first, second)

theorem splitInvariantInflation_apply {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ (splitInvariantRepresentation splitting representation)) :
    splitInvariantInflation splitting representation
        (groupCohomology.H2π (splitInvariantRepresentation splitting representation) cycle) =
      groupCohomology.H2π representation (splitInflatedCocycle splitting representation cycle) :=
  groupCohomology.H2π_comp_map_apply extension.rightHom (splitInvariantInclusion splitting representation) cycle

end TernaryPeriodPolynomials.SphericalDetection.Helpers
