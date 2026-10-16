module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CochainCoordinates

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

theorem splitEdgeCycle_one {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation) :
    splitEdgeCycle splitting representation 1 cycle = 0 := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  rw [splitEdgeCycle_apply, map_one, relativeTwoCocycle_one_left, relativeTwoCocycle_one_right, sub_self]
  rfl

theorem splitEdgeCycle_relativeBoundary_H1 {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (primitive : E → representation)
    (restriction : groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (agrees : ∀ radical, primitive (extension.inl radical) = restriction radical) (levi : L) :
    groupCohomology.H1π (Rep.res extension.inl representation)
      (splitEdgeCycle splitting representation levi
        (relativeBoundaryOfRestriction extension.inl representation primitive restriction agrees)) =
      splitRadicalH1Action splitting representation levi
        (groupCohomology.H1π (Rep.res extension.inl representation) restriction) -
        groupCohomology.H1π (Rep.res extension.inl representation) restriction := by
  rw [splitEdgeCycle_relativeBoundary, map_sub, map_sub, oneBoundaryCycle_H1_zero, sub_zero,
    splitRadicalH1Action_apply]

/-- A zero edge class admits a relative representative with every mixed radical class zero. -/
theorem splitEdge_class_normalization {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (zero : groupCohomology.H1π (splitRadicalH1Representation splitting representation)
      (splitCocycleEdge splitting representation cycle) = 0) :
    ∃ normalized : relativeTwoCocycles extension.inl representation,
      groupCohomology.H2π representation normalized.val = groupCohomology.H2π representation cycle.val ∧
      ∀ levi, groupCohomology.H1π (Rep.res extension.inl representation)
        (splitEdgeCycle splitting representation levi normalized) = 0 := by
  rw [groupCohomology.H1π_eq_zero_iff] at zero
  obtain ⟨potential, boundary⟩ := zero
  change groupCohomology.H1 (Rep.res extension.inl representation) at potential
  obtain ⟨radical_cycle, representative⟩ := oneCocycle_H1_surjective (Rep.res extension.inl representation) potential
  let primitive := splitExtendRadicalCycle splitting representation radical_cycle
  let correction := relativeBoundaryOfRestriction extension.inl representation primitive radical_cycle
    (splitExtendRadicalCycle_inl splitting representation radical_cycle)
  refine ⟨cycle - correction, ?_, ?_⟩
  · change groupCohomology.H2π representation (cycle.val - correction.val) = _
    rw [map_sub, relativeBoundaryOfRestriction_H2_zero, sub_zero]
  · intro levi
    rw [(splitEdgeCycle splitting representation levi).map_sub cycle correction, map_sub]
    have mixed : groupCohomology.H1π (Rep.res extension.inl representation)
        (splitEdgeCycle splitting representation levi correction) =
        splitRadicalH1Action splitting representation levi potential - potential := by
      rw [splitEdgeCycle_relativeBoundary_H1, representative]
    rw [mixed]
    have equation := congrFun boundary levi
    change splitRadicalH1Action splitting representation levi potential - potential =
      groupCohomology.H1π (Rep.res extension.inl representation)
        (splitEdgeCycle splitting representation levi cycle) at equation
    rw [equation, sub_self]

/-- Pointwise zero mixed classes can be made literally zero by a second coboundary. -/
theorem splitEdge_pointwise_normalization {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (zero : ∀ levi, groupCohomology.H1π (Rep.res extension.inl representation)
      (splitEdgeCycle splitting representation levi cycle) = 0) :
    ∃ normalized : relativeTwoCocycles extension.inl representation,
      groupCohomology.H2π representation normalized.val = groupCohomology.H2π representation cycle.val ∧
      ∀ levi, splitEdgeCycle splitting representation levi normalized = 0 := by
  classical
  have potentials (levi : L) : ∃ potential : representation,
      oneBoundaryCycle (Rep.res extension.inl representation) potential =
        splitEdgeCycle splitting representation levi cycle ∧ (levi = 1 → potential = 0) := by
    by_cases identity : levi = 1
    · subst levi
      refine ⟨0, ?_, fun _ => rfl⟩
      rw [splitEdgeCycle_one]
      apply groupCohomology.cocycles₁_ext
      intro radical
      simp only [oneBoundaryCycle_apply, map_zero, sub_self]
      rfl
    · obtain ⟨potential, boundary⟩ := (groupCohomology.H1π_eq_zero_iff _).mp (zero levi)
      exact ⟨potential, Subtype.ext boundary, fun equality => (identity equality).elim⟩
  choose potential potential_boundary potential_one using potentials
  let primitive : E → representation := fun element => potential (extension.rightHom element)
  have radical_zero (radical : N) : primitive (extension.inl radical) =
      (0 : groupCohomology.cocycles₁ (Rep.res extension.inl representation)) radical := by
    change potential (extension.rightHom (extension.inl radical)) = 0
    rw [extension.rightHom_inl, potential_one 1 rfl]
  let correction := relativeBoundaryOfRestriction extension.inl representation primitive 0 radical_zero
  refine ⟨cycle + correction, ?_, ?_⟩
  · change groupCohomology.H2π representation (cycle.val + correction.val) = _
    rw [map_add, relativeBoundaryOfRestriction_H2_zero, add_zero]
  · intro levi
    rw [(splitEdgeCycle splitting representation levi).map_add]
    have mixed : splitEdgeCycle splitting representation levi correction =
        -splitEdgeCycle splitting representation levi cycle := by
      rw [splitEdgeCycle_relativeBoundary, map_zero, sub_zero, zero_sub]
      change -oneBoundaryCycle (Rep.res extension.inl representation)
        (potential (extension.rightHom (splitting levi))) = _
      rw [splitting.rightHom_splitting, potential_boundary]
    rw [mixed, add_neg_cancel]

theorem splitEdge_zero_representative {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (zero : groupCohomology.H1π (splitRadicalH1Representation splitting representation)
      (splitCocycleEdge splitting representation cycle) = 0) :
    ∃ normalized : relativeTwoCocycles extension.inl representation,
      groupCohomology.H2π representation normalized.val = groupCohomology.H2π representation cycle.val ∧
      ∀ levi, splitEdgeCycle splitting representation levi normalized = 0 := by
  obtain ⟨first, same_class, pointwise⟩ := splitEdge_class_normalization splitting representation cycle zero
  obtain ⟨second, same_class', literal⟩ := splitEdge_pointwise_normalization splitting representation first pointwise
  exact ⟨second, same_class'.trans same_class, literal⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
