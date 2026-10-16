module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CocycleEdge

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

def relativeBoundaryRadicalCycle (inclusion : N →* E) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles inclusion representation) (primitive : E → representation)
    (boundary : ∀ first second : E,
      representation.ρ first (primitive second) - primitive (first * second) + primitive first = cycle.val (first, second)) :
    groupCohomology.cocycles₁ (Rep.res inclusion representation) :=
  ⟨fun radical => primitive (inclusion radical), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro first second
    have equation := boundary (inclusion first) (inclusion second)
    rw [cycle.property, ← map_mul] at equation
    change primitive (inclusion (first * second)) =
      representation.ρ (inclusion first) (primitive (inclusion second)) + primitive (inclusion first)
    linear_combination (norm := abel) -equation⟩

theorem relativeBoundaryRadicalCycle_apply (inclusion : N →* E) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles inclusion representation) (primitive : E → representation)
    (boundary : ∀ first second : E,
      representation.ρ first (primitive second) - primitive (first * second) + primitive first = cycle.val (first, second))
    (radical : N) : relativeBoundaryRadicalCycle inclusion representation cycle primitive boundary radical =
      primitive (inclusion radical) := rfl

theorem splitEdgeCycle_boundary {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (element : L) (cycle : relativeTwoCocycles extension.inl representation)
    (primitive : E → representation)
    (boundary : ∀ first second : E,
      representation.ρ first (primitive second) - primitive (first * second) + primitive first = cycle.val (first, second)) :
    splitEdgeCycle splitting representation element cycle =
      splitRadicalCocycleAction splitting representation element
          (relativeBoundaryRadicalCycle extension.inl representation cycle primitive boundary) -
        relativeBoundaryRadicalCycle extension.inl representation cycle primitive boundary -
        oneBoundaryCycle (Rep.res extension.inl representation) (primitive (splitting element)) := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  change splitEdgeCycle splitting representation element cycle radical =
    splitRadicalCocycleAction splitting representation element
        (relativeBoundaryRadicalCycle extension.inl representation cycle primitive boundary) radical -
      relativeBoundaryRadicalCycle extension.inl representation cycle primitive boundary radical -
      oneBoundaryCycle (Rep.res extension.inl representation) (primitive (splitting element)) radical
  rw [splitEdgeCycle_apply,
    ← boundary (splitting element) (extension.inl (splitRadicalInput splitting element radical)),
    ← boundary (extension.inl radical) (splitting element), ← splitRadicalInput_commute]
  simp only [splitRadicalCocycleAction_apply, relativeBoundaryRadicalCycle_apply, oneBoundaryCycle_apply,
    MonoidHom.comp_apply]
  abel

theorem splitCocycleEdge_H1_zero_of_boundary {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (primitive : E → representation)
    (boundary : ∀ first second : E,
      representation.ρ first (primitive second) - primitive (first * second) + primitive first = cycle.val (first, second)) :
    groupCohomology.H1π (splitRadicalH1Representation splitting representation)
      (splitCocycleEdge splitting representation cycle) = 0 := by
  rw [groupCohomology.H1π_eq_zero_iff]
  refine ⟨groupCohomology.H1π (Rep.res extension.inl representation)
    (relativeBoundaryRadicalCycle extension.inl representation cycle primitive boundary), ?_⟩
  funext element
  change splitRadicalH1Action splitting representation element
      (groupCohomology.H1π (Rep.res extension.inl representation)
        (relativeBoundaryRadicalCycle extension.inl representation cycle primitive boundary)) -
      groupCohomology.H1π (Rep.res extension.inl representation)
        (relativeBoundaryRadicalCycle extension.inl representation cycle primitive boundary) =
    splitCocycleEdge splitting representation cycle element
  rw [splitCocycleEdge_apply, splitEdgeCycle_boundary splitting representation element cycle primitive boundary,
    map_sub, map_sub, oneBoundaryCycle_H1_zero, sub_zero, splitRadicalH1Action_apply]

theorem splitCocycleEdge_H1_zero_of_H2_zero {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (zero : groupCohomology.H2π representation cycle.val = 0) :
    groupCohomology.H1π (splitRadicalH1Representation splitting representation)
      (splitCocycleEdge splitting representation cycle) = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff] at zero
  obtain ⟨primitive, boundary⟩ := zero
  change E → representation at primitive
  apply splitCocycleEdge_H1_zero_of_boundary splitting representation cycle primitive
  intro first second
  exact congrFun boundary (first, second)

theorem splitCocycleEdge_H1_eq_of_H2_eq {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (first second : relativeTwoCocycles extension.inl representation)
    (equality : groupCohomology.H2π representation first.val = groupCohomology.H2π representation second.val) :
    groupCohomology.H1π (splitRadicalH1Representation splitting representation)
        (splitCocycleEdge splitting representation first) =
      groupCohomology.H1π (splitRadicalH1Representation splitting representation)
        (splitCocycleEdge splitting representation second) := by
  have zero : groupCohomology.H2π representation (first - second).val = 0 := by
    change groupCohomology.H2π representation (first.val - second.val) = 0
    rw [map_sub, equality, sub_self]
  have edge_zero := splitCocycleEdge_H1_zero_of_H2_zero splitting representation (first - second) zero
  rw [(splitCocycleEdge splitting representation).map_sub first second, map_sub, sub_eq_zero] at edge_zero
  exact edge_zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
