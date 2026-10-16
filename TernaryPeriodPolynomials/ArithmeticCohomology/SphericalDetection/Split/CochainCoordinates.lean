module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CohomologyEdge

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

theorem splitSemidirect_apply {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (radical : N) (levi : L) :
    splitting.semidirectProductMulEquiv ⟨radical, levi⟩ = extension.inl radical * splitting levi := rfl

def splitRadicalCoordinate {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (element : E) : N := (splitting.semidirectProductMulEquiv.symm element).left

theorem splitRadicalCoordinate_pair {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (radical : N) (levi : L) :
    splitRadicalCoordinate splitting (extension.inl radical * splitting levi) = radical := by
  rw [← splitSemidirect_apply splitting radical levi]
  exact congrArg SemidirectProduct.left (splitting.semidirectProductMulEquiv.symm_apply_apply ⟨radical, levi⟩)

theorem splitRadicalCoordinate_inl {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (radical : N) : splitRadicalCoordinate splitting (extension.inl radical) = radical := by
  simpa only [map_one, mul_one] using splitRadicalCoordinate_pair splitting radical 1

theorem splitRadicalCoordinate_splitting {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (levi : L) : splitRadicalCoordinate splitting (splitting levi) = 1 := by
  simpa only [map_one, one_mul] using splitRadicalCoordinate_pair splitting 1 levi

theorem split_exists_pair {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (element : E) : ∃ radical levi, element = extension.inl radical * splitting levi := by
  obtain ⟨⟨radical, levi⟩, equality⟩ := splitting.semidirectProductMulEquiv.surjective element
  exact ⟨radical, levi, equality.symm⟩

theorem split_coordinate_decomposition {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (element : E) :
    extension.inl (splitRadicalCoordinate splitting element) * splitting (extension.rightHom element) = element := by
  obtain ⟨radical, levi, rfl⟩ := split_exists_pair splitting element
  rw [splitRadicalCoordinate_pair, map_mul, extension.rightHom_inl,
    splitting.rightHom_splitting, one_mul]

theorem relativeTwoCocycle_one_left (inclusion : N →* E) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles inclusion representation) (element : E) : cycle.val (1, element) = 0 := by
  have zero : cycle.val (1, 1) = 0 := by simpa only [map_one] using cycle.property 1 1
  have equation := twoCocycle_relation representation cycle.val 1 1 element
  simp only [one_mul, map_one, Module.End.one_apply, zero, add_zero] at equation
  linear_combination (norm := abel) -equation

theorem relativeTwoCocycle_one_right (inclusion : N →* E) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles inclusion representation) (element : E) : cycle.val (element, 1) = 0 := by
  have equation := twoCocycle_relation representation cycle.val element 1 1
  rw [relativeTwoCocycle_one_left inclusion representation cycle, map_zero] at equation
  simp only [mul_one, zero_add] at equation
  linear_combination (norm := abel) equation

/-- Extend a radical cocycle along the radical coordinate of the splitting. -/
def splitExtendRadicalCycle {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation)) :
    E → representation := fun element => cycle (splitRadicalCoordinate splitting element)

theorem splitExtendRadicalCycle_inl {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (radical : N) : splitExtendRadicalCycle splitting representation cycle (extension.inl radical) = cycle radical := by
  exact congrArg cycle (splitRadicalCoordinate_inl splitting radical)

theorem splitExtendRadicalCycle_splitting {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (levi : L) : splitExtendRadicalCycle splitting representation cycle (splitting levi) = 0 := by
  change cycle (splitRadicalCoordinate splitting (splitting levi)) = 0
  rw [splitRadicalCoordinate_splitting, groupCohomology.cocycles₁_map_one]

/-- A boundary is relative whenever its restricted one-cochain is a cocycle. -/
def relativeBoundaryOfRestriction (inclusion : N →* E) (representation : Rep ℂ E)
    (primitive : E → representation) (restriction : groupCohomology.cocycles₁ (Rep.res inclusion representation))
    (agrees : ∀ radical, primitive (inclusion radical) = restriction radical) :
    relativeTwoCocycles inclusion representation :=
  ⟨twoBoundaryCycle representation primitive, by
    intro first second
    rw [twoBoundaryCycle_apply, ← map_mul, agrees, agrees, agrees]
    have equation := (groupCohomology.mem_cocycles₁_iff _).mp restriction.property first second
    change restriction (first * second) = representation.ρ (inclusion first) (restriction second) + restriction first at equation
    rw [equation]
    abel⟩

theorem relativeBoundaryOfRestriction_H2_zero (inclusion : N →* E) (representation : Rep ℂ E)
    (primitive : E → representation) (restriction : groupCohomology.cocycles₁ (Rep.res inclusion representation))
    (agrees : ∀ radical, primitive (inclusion radical) = restriction radical) :
    groupCohomology.H2π representation
      (relativeBoundaryOfRestriction inclusion representation primitive restriction agrees).val = 0 :=
  twoBoundaryCycle_H2_zero representation primitive

theorem splitEdgeCycle_relativeBoundary {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (primitive : E → representation)
    (restriction : groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (agrees : ∀ radical, primitive (extension.inl radical) = restriction radical) (levi : L) :
    splitEdgeCycle splitting representation levi
        (relativeBoundaryOfRestriction extension.inl representation primitive restriction agrees) =
      splitRadicalCocycleAction splitting representation levi restriction - restriction -
        oneBoundaryCycle (Rep.res extension.inl representation) (primitive (splitting levi)) := by
  rw [splitEdgeCycle_boundary splitting representation levi _ primitive (fun _ _ => rfl)]
  have same : relativeBoundaryRadicalCycle extension.inl representation
      (relativeBoundaryOfRestriction extension.inl representation primitive restriction agrees)
      primitive (fun _ _ => rfl) = restriction := by
    apply groupCohomology.cocycles₁_ext
    exact agrees
  rw [same]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
