module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.RadicalAction

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

theorem twoCocycle_relation (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ representation)
    (first second third : E) :
    cycle (first * second, third) + cycle (first, second) =
      representation.ρ first (cycle (second, third)) + cycle (first, second * third) :=
  (groupCohomology.mem_cocycles₂_iff _).mp cycle.property first second third

def oneBoundaryCycle (representation : Rep ℂ N) (potential : representation) :
    groupCohomology.cocycles₁ representation :=
  ⟨groupCohomology.d₀₁ representation potential, groupCohomology.d₀₁_apply_mem_cocycles₁ potential⟩

theorem oneBoundaryCycle_apply (representation : Rep ℂ N) (potential : representation) (element : N) :
    oneBoundaryCycle representation potential element = representation.ρ element potential - potential := rfl

theorem oneBoundaryCycle_H1_zero (representation : Rep ℂ N) (potential : representation) :
    groupCohomology.H1π representation (oneBoundaryCycle representation potential) = 0 := by
  rw [groupCohomology.H1π_eq_zero_iff]
  exact ⟨potential, rfl⟩

/-- Two-cocycles that vanish on pairs of radical elements. -/
def relativeTwoCocycles (inclusion : N →* E) (representation : Rep ℂ E) :
    Submodule ℂ (groupCohomology.cocycles₂ representation) where
  carrier := {cycle | ∀ first second : N, cycle (inclusion first, inclusion second) = 0}
  zero_mem' := by
    intro first second
    rfl
  add_mem' {first second} first_zero second_zero := by
    intro left right
    change first (inclusion left, inclusion right) + second (inclusion left, inclusion right) = 0
    rw [first_zero left right, second_zero left right, add_zero]
  smul_mem' scalar cycle zero := by
    intro left right
    change scalar • cycle (inclusion left, inclusion right) = 0
    rw [zero left right, smul_zero]

/-- The mixed part of a relative two-cocycle is a radical one-cocycle. -/
def splitEdgeCycle {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (element : L) :
    relativeTwoCocycles extension.inl representation →ₗ[ℂ]
      groupCohomology.cocycles₁ (Rep.res extension.inl representation) where
  toFun cycle := ⟨fun radical =>
    cycle.val (splitting element, extension.inl (splitRadicalInput splitting element radical)) -
      cycle.val (extension.inl radical, splitting element), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro first second
    have relation0 := twoCocycle_relation representation cycle.val (splitting element)
      (extension.inl (splitRadicalInput splitting element first))
      (extension.inl (splitRadicalInput splitting element second))
    have relation1 := twoCocycle_relation representation cycle.val (extension.inl first)
      (splitting element) (extension.inl (splitRadicalInput splitting element second))
    have relation2 := twoCocycle_relation representation cycle.val (extension.inl first)
      (extension.inl second) (splitting element)
    rw [cycle.property, map_zero, zero_add, ← splitRadicalInput_commute] at relation0
    rw [← splitRadicalInput_commute] at relation1
    rw [cycle.property, add_zero] at relation2
    change cycle.val (splitting element, extension.inl (splitRadicalInput splitting element (first * second))) -
        cycle.val (extension.inl (first * second), splitting element) =
      representation.ρ (extension.inl first)
        (cycle.val (splitting element, extension.inl (splitRadicalInput splitting element second)) -
          cycle.val (extension.inl second, splitting element)) +
        (cycle.val (splitting element, extension.inl (splitRadicalInput splitting element first)) -
          cycle.val (extension.inl first, splitting element))
    rw [map_mul, map_mul, map_mul, map_sub]
    linear_combination (norm := abel) -relation0 + relation1 - relation2⟩
  map_add' first second := by
    apply groupCohomology.cocycles₁_ext
    intro radical
    change (first.val (splitting element, extension.inl (splitRadicalInput splitting element radical)) +
        second.val (splitting element, extension.inl (splitRadicalInput splitting element radical))) -
      (first.val (extension.inl radical, splitting element) + second.val (extension.inl radical, splitting element)) =
      (first.val (splitting element, extension.inl (splitRadicalInput splitting element radical)) -
        first.val (extension.inl radical, splitting element)) +
      (second.val (splitting element, extension.inl (splitRadicalInput splitting element radical)) -
        second.val (extension.inl radical, splitting element))
    abel
  map_smul' scalar cycle := by
    apply groupCohomology.cocycles₁_ext
    intro radical
    change scalar • cycle.val (splitting element, extension.inl (splitRadicalInput splitting element radical)) -
      scalar • cycle.val (extension.inl radical, splitting element) =
      scalar • (cycle.val (splitting element, extension.inl (splitRadicalInput splitting element radical)) -
        cycle.val (extension.inl radical, splitting element))
    exact (smul_sub scalar _ _).symm

theorem splitEdgeCycle_apply {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (element : L) (cycle : relativeTwoCocycles extension.inl representation)
    (radical : N) :
    splitEdgeCycle splitting representation element cycle radical =
      cycle.val (splitting element, extension.inl (splitRadicalInput splitting element radical)) -
        cycle.val (extension.inl radical, splitting element) := rfl

theorem splitEdgeCycle_mul {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (first second : L) (cycle : relativeTwoCocycles extension.inl representation) :
    splitEdgeCycle splitting representation (first * second) cycle =
      splitRadicalCocycleAction splitting representation first (splitEdgeCycle splitting representation second cycle) +
        splitEdgeCycle splitting representation first cycle +
        oneBoundaryCycle (Rep.res extension.inl representation) (cycle.val (splitting first, splitting second)) := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  have relation0 := twoCocycle_relation representation cycle.val (splitting first) (splitting second)
    (extension.inl (splitRadicalInput splitting second (splitRadicalInput splitting first radical)))
  have relation1 := twoCocycle_relation representation cycle.val (splitting first)
    (extension.inl (splitRadicalInput splitting first radical)) (splitting second)
  have relation2 := twoCocycle_relation representation cycle.val (extension.inl radical) (splitting first) (splitting second)
  rw [← splitRadicalInput_commute] at relation0 relation1
  change splitEdgeCycle splitting representation (first * second) cycle radical =
    splitRadicalCocycleAction splitting representation first (splitEdgeCycle splitting representation second cycle) radical +
      splitEdgeCycle splitting representation first cycle radical +
      oneBoundaryCycle (Rep.res extension.inl representation) (cycle.val (splitting first, splitting second)) radical
  simp only [splitEdgeCycle_apply, splitRadicalCocycleAction_apply, oneBoundaryCycle_apply,
    splitRadicalInput_mul, map_mul, map_sub, MonoidHom.comp_apply]
  linear_combination (norm := abel) relation0 - relation1 + relation2

/-- The mixed radical classes form an actual Levi one-cocycle. -/
def splitCocycleEdge {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) :
    relativeTwoCocycles extension.inl representation →ₗ[ℂ]
      groupCohomology.cocycles₁ (splitRadicalH1Representation splitting representation) :=
  (LinearMap.pi (fun element =>
    (groupCohomology.H1π (Rep.res extension.inl representation)).hom.comp
      (splitEdgeCycle splitting representation element))).codRestrict _ (by
    intro cycle
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro first second
    change groupCohomology.H1π (Rep.res extension.inl representation)
      (splitEdgeCycle splitting representation (first * second) cycle) = _
    rw [splitEdgeCycle_mul, map_add, map_add, oneBoundaryCycle_H1_zero, add_zero]
    change groupCohomology.H1π (Rep.res extension.inl representation)
        (splitRadicalCocycleAction splitting representation first (splitEdgeCycle splitting representation second cycle)) + _ =
      splitRadicalH1Action splitting representation first _ + _
    simp only [LinearMap.pi_apply, LinearMap.comp_apply]
    rw [splitRadicalH1Action_apply])

theorem splitCocycleEdge_apply {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation) (element : L) :
    splitCocycleEdge splitting representation cycle element =
      groupCohomology.H1π (Rep.res extension.inl representation) (splitEdgeCycle splitting representation element cycle) := rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
