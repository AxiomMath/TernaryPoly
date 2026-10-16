module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.EdgeNormalization

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

def splitMixedPrimitive {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation) : E → representation :=
  fun element => cycle.val
    (extension.inl (splitRadicalCoordinate splitting element), splitting (extension.rightHom element))

theorem splitMixedPrimitive_pair {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (radical : N) (levi : L) :
    splitMixedPrimitive splitting representation cycle (extension.inl radical * splitting levi) =
      cycle.val (extension.inl radical, splitting levi) := by
  unfold splitMixedPrimitive
  rw [splitRadicalCoordinate_pair, map_mul, extension.rightHom_inl, splitting.rightHom_splitting, one_mul]

theorem splitMixedPrimitive_inl {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation) (radical : N) :
    splitMixedPrimitive splitting representation cycle (extension.inl radical) = 0 := by
  have equality := splitMixedPrimitive_pair splitting representation cycle radical 1
  simpa only [map_one, mul_one, relativeTwoCocycle_one_right] using equality

theorem splitMixedPrimitive_splitting {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation) (levi : L) :
    splitMixedPrimitive splitting representation cycle (splitting levi) = 0 := by
  have equality := splitMixedPrimitive_pair splitting representation cycle 1 levi
  simpa only [map_one, one_mul, relativeTwoCocycle_one_left] using equality

theorem splitMixed_normalization {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (zero : ∀ levi, splitEdgeCycle splitting representation levi cycle = 0) :
    ∃ normalized : relativeTwoCocycles extension.inl representation,
      groupCohomology.H2π representation normalized.val = groupCohomology.H2π representation cycle.val ∧
      (∀ levi, splitEdgeCycle splitting representation levi normalized = 0) ∧
      ∀ radical levi, normalized.val (extension.inl radical, splitting levi) = 0 := by
  let primitive := splitMixedPrimitive splitting representation cycle
  let correction := relativeBoundaryOfRestriction extension.inl representation primitive 0
    (splitMixedPrimitive_inl splitting representation cycle)
  refine ⟨cycle + correction, ?_, ?_, ?_⟩
  · change groupCohomology.H2π representation (cycle.val + correction.val) = _
    rw [map_add, relativeBoundaryOfRestriction_H2_zero, add_zero]
  · intro levi
    rw [(splitEdgeCycle splitting representation levi).map_add, zero, zero_add]
    rw [splitEdgeCycle_relativeBoundary, map_zero, sub_zero]
    apply groupCohomology.cocycles₁_ext
    intro radical
    change 0 - (representation.ρ (extension.inl radical) (primitive (splitting levi)) -
      primitive (splitting levi)) = 0
    dsimp only [primitive]
    rw [splitMixedPrimitive_splitting, map_zero, sub_self, sub_self]
  · intro radical levi
    change cycle.val (extension.inl radical, splitting levi) +
      twoBoundaryCycle representation primitive (extension.inl radical, splitting levi) = 0
    dsimp only [primitive]
    rw [twoBoundaryCycle_apply, splitMixedPrimitive_inl, splitMixedPrimitive_splitting,
      splitMixedPrimitive_pair, map_zero]
    abel

theorem relativeTwoCocycle_radical_left {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (mixed : ∀ radical levi, cycle.val (extension.inl radical, splitting levi) = 0)
    (radical : N) (element : E) : cycle.val (extension.inl radical, element) = 0 := by
  obtain ⟨other, levi, rfl⟩ := split_exists_pair splitting element
  have equation := twoCocycle_relation representation cycle.val (extension.inl radical)
    (extension.inl other) (splitting levi)
  rw [← map_mul, mixed, cycle.property, mixed, map_zero, add_zero, zero_add] at equation
  exact equation.symm

theorem relativeTwoCocycle_levi_radical {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (zero : ∀ levi, splitEdgeCycle splitting representation levi cycle = 0)
    (mixed : ∀ radical levi, cycle.val (extension.inl radical, splitting levi) = 0)
    (levi : L) (radical : N) : cycle.val (splitting levi, extension.inl radical) = 0 := by
  obtain ⟨other, preimage⟩ := (splitting.conjAct levi⁻¹).surjective radical
  have equation := congrArg (fun cocycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation) => cocycle other)
    (zero levi)
  change cycle.val (splitting levi, extension.inl (splitRadicalInput splitting levi other)) -
    cycle.val (extension.inl other, splitting levi) = 0 at equation
  rw [mixed, sub_zero] at equation
  exact (congrArg (fun input => cycle.val (splitting levi, extension.inl input)) preimage).symm.trans equation

theorem relativeTwoCocycle_radical_right {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (zero : ∀ levi, splitEdgeCycle splitting representation levi cycle = 0)
    (mixed : ∀ radical levi, cycle.val (extension.inl radical, splitting levi) = 0)
    (element : E) (radical : N) : cycle.val (element, extension.inl radical) = 0 := by
  obtain ⟨other, levi, rfl⟩ := split_exists_pair splitting element
  have equation := twoCocycle_relation representation cycle.val (extension.inl other)
    (splitting levi) (extension.inl radical)
  rw [mixed, relativeTwoCocycle_levi_radical splitting representation cycle zero mixed,
    map_zero, relativeTwoCocycle_radical_left splitting representation cycle mixed, add_zero, add_zero] at equation
  exact equation

/-- Every relative class with zero edge has a representative zero when either argument is radical. -/
theorem splitEdge_radical_normalization {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (zero : groupCohomology.H1π (splitRadicalH1Representation splitting representation)
      (splitCocycleEdge splitting representation cycle) = 0) :
    ∃ normalized : groupCohomology.cocycles₂ representation,
      groupCohomology.H2π representation normalized = groupCohomology.H2π representation cycle.val ∧
      (∀ radical element, normalized (extension.inl radical, element) = 0) ∧
      ∀ element radical, normalized (element, extension.inl radical) = 0 := by
  obtain ⟨first, first_class, first_zero⟩ := splitEdge_zero_representative splitting representation cycle zero
  obtain ⟨second, second_class, second_zero, mixed⟩ := splitMixed_normalization splitting representation first first_zero
  exact ⟨second.val, second_class.trans first_class,
    relativeTwoCocycle_radical_left splitting representation second mixed,
    relativeTwoCocycle_radical_right splitting representation second second_zero mixed⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
