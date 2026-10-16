module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CocycleEdgeBoundary

@[expose] public section


open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E : Type} [Group N] [Group E]

def twoBoundaryCycle (representation : Rep ℂ E) (primitive : E → representation) :
    groupCohomology.cocycles₂ representation :=
  ⟨groupCohomology.d₁₂ representation primitive, groupCohomology.d₁₂_apply_mem_cocycles₂ primitive⟩

theorem twoBoundaryCycle_apply (representation : Rep ℂ E) (primitive : E → representation) (first second : E) :
    twoBoundaryCycle representation primitive (first, second) =
      representation.ρ first (primitive second) - primitive (first * second) + primitive first := rfl

theorem twoBoundaryCycle_H2_zero (representation : Rep ℂ E) (primitive : E → representation) :
    groupCohomology.H2π representation (twoBoundaryCycle representation primitive) = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff]
  exact ⟨primitive, rfl⟩

def twoCocycleRestriction (inclusion : N →* E) (representation : Rep ℂ E) :
    groupCohomology.cocycles₂ representation →ₗ[ℂ] groupCohomology.cocycles₂ (Rep.res inclusion representation) where
  toFun cycle := ⟨fun pair => cycle (inclusion pair.1, inclusion pair.2), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro first second third
    change cycle (inclusion (first * second), inclusion third) + cycle (inclusion first, inclusion second) =
      representation.ρ (inclusion first) (cycle (inclusion second, inclusion third)) +
        cycle (inclusion first, inclusion (second * third))
    rw [map_mul, map_mul]
    exact twoCocycle_relation representation cycle _ _ _⟩
  map_add' first second := by
    apply Subtype.ext
    rfl
  map_smul' scalar cycle := by
    apply Subtype.ext
    rfl

theorem twoCocycleRestriction_apply (inclusion : N →* E) (representation : Rep ℂ E)
    (cycle : groupCohomology.cocycles₂ representation) (first second : N) :
    twoCocycleRestriction inclusion representation cycle (first, second) =
      cycle (inclusion first, inclusion second) := rfl

theorem twoCocycleRestriction_eq_mapCocycles (inclusion : N →* E) (representation : Rep ℂ E)
    (cycle : groupCohomology.cocycles₂ representation) :
    groupCohomology.mapCocycles₂ inclusion (𝟙 (Rep.res inclusion representation)) cycle =
      twoCocycleRestriction inclusion representation cycle := by
  apply Subtype.ext
  have equality := groupCohomology.mapCocycles₂_comp_i_apply inclusion (𝟙 (Rep.res inclusion representation)) cycle
  exact equality

def twoCohomologyRestriction (inclusion : N →* E) (representation : Rep ℂ E) :
    groupCohomology.H2 representation →ₗ[ℂ] groupCohomology.H2 (Rep.res inclusion representation) :=
  (groupCohomology.map inclusion (𝟙 (Rep.res inclusion representation)) 2).hom

theorem twoCohomologyRestriction_apply (inclusion : N →* E) (representation : Rep ℂ E)
    (cycle : groupCohomology.cocycles₂ representation) :
    twoCohomologyRestriction inclusion representation (groupCohomology.H2π representation cycle) =
      groupCohomology.H2π (Rep.res inclusion representation) (twoCocycleRestriction inclusion representation cycle) := by
  change groupCohomology.map inclusion (𝟙 (Rep.res inclusion representation)) 2
    (groupCohomology.H2π representation cycle) = _
  rw [groupCohomology.H2π_comp_map_apply, twoCocycleRestriction_eq_mapCocycles]

/-- A radical primitive can be extended as a one-cochain on the whole group. -/
def extendRadicalPrimitive (inclusion : N →* E) (representation : Rep ℂ E)
    (primitive : N → representation) : E → representation :=
  fun element => primitive (Function.invFun inclusion element)

theorem extendRadicalPrimitive_apply (inclusion : N →* E) (injective : Function.Injective inclusion)
    (representation : Rep ℂ E) (primitive : N → representation) (radical : N) :
    extendRadicalPrimitive inclusion representation primitive (inclusion radical) = primitive radical := by
  unfold extendRadicalPrimitive
  rw [Function.leftInverse_invFun injective]

/-- Vanishing of the restricted H2 class gives a representative that vanishes literally on radical pairs. -/
theorem relativeTwoCocycleRepresentative_exists (inclusion : N →* E) (injective : Function.Injective inclusion)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ representation)
    (zero : groupCohomology.H2π (Rep.res inclusion representation)
      (twoCocycleRestriction inclusion representation cycle) = 0) :
    ∃ relative : relativeTwoCocycles inclusion representation,
      groupCohomology.H2π representation relative.val = groupCohomology.H2π representation cycle := by
  rw [groupCohomology.H2π_eq_zero_iff] at zero
  obtain ⟨primitive, boundary⟩ := zero
  change N → representation at primitive
  let extended := extendRadicalPrimitive inclusion representation primitive
  have radical_boundary (first second : N) :
      twoBoundaryCycle representation extended (inclusion first, inclusion second) =
        cycle (inclusion first, inclusion second) := by
    rw [twoBoundaryCycle_apply, ← map_mul]
    dsimp only [extended]
    rw [extendRadicalPrimitive_apply inclusion injective,
      extendRadicalPrimitive_apply inclusion injective, extendRadicalPrimitive_apply inclusion injective]
    exact congrFun boundary (first, second)
  let relative : relativeTwoCocycles inclusion representation :=
    ⟨cycle - twoBoundaryCycle representation extended, by
      intro first second
      change cycle (inclusion first, inclusion second) -
        twoBoundaryCycle representation extended (inclusion first, inclusion second) = 0
      rw [radical_boundary, sub_self]⟩
  refine ⟨relative, ?_⟩
  change groupCohomology.H2π representation (cycle - twoBoundaryCycle representation extended) = _
  rw [map_sub, twoBoundaryCycle_H2_zero, sub_zero]

theorem relativeTwoCocycle_restriction_zero (inclusion : N →* E) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles inclusion representation) :
    twoCocycleRestriction inclusion representation cycle.val = 0 := by
  apply Subtype.ext
  funext pair
  exact cycle.property pair.1 pair.2

theorem relativeTwoCocycle_class_restriction_zero (inclusion : N →* E) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles inclusion representation) :
    twoCohomologyRestriction inclusion representation (groupCohomology.H2π representation cycle.val) = 0 := by
  rw [twoCohomologyRestriction_apply, relativeTwoCocycle_restriction_zero, map_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
