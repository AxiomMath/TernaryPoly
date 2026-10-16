module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CochainCoordinates

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

theorem splitRadicalCoordinate_mul {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (first second : E) :
    splitRadicalCoordinate splitting (first * second) =
      splitRadicalCoordinate splitting first *
        splitting.conjAct (extension.rightHom first) (splitRadicalCoordinate splitting second) := by
  obtain ⟨left, right, rfl⟩ := split_exists_pair splitting first
  obtain ⟨left', right', rfl⟩ := split_exists_pair splitting second
  rw [splitRadicalCoordinate_pair, splitRadicalCoordinate_pair, map_mul,
    extension.rightHom_inl, splitting.rightHom_splitting, one_mul]
  change (splitting.semidirectProductMulEquiv.symm
    (splitting.semidirectProductMulEquiv ⟨left, right⟩ *
      splitting.semidirectProductMulEquiv ⟨left', right'⟩)).left = _
  rw [map_mul, splitting.semidirectProductMulEquiv.symm_apply_apply,
    splitting.semidirectProductMulEquiv.symm_apply_apply]
  rfl

/-- A cocycle invariant under the splitting extends along its radical coordinate. -/
def splitInvariantOneCocycle {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (invariant : ∀ levi radical, cycle (splitting.conjAct levi radical) =
      representation.ρ (splitting levi) (cycle radical)) :
    groupCohomology.cocycles₁ representation :=
  ⟨splitExtendRadicalCycle splitting representation cycle, by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro first second
    change cycle (splitRadicalCoordinate splitting (first * second)) =
      representation.ρ first (cycle (splitRadicalCoordinate splitting second)) +
        cycle (splitRadicalCoordinate splitting first)
    rw [splitRadicalCoordinate_mul]
    have relation := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property
      (splitRadicalCoordinate splitting first)
      (splitting.conjAct (extension.rightHom first) (splitRadicalCoordinate splitting second))
    change cycle (_ * _) = representation.ρ (extension.inl (splitRadicalCoordinate splitting first))
      (cycle (splitting.conjAct (extension.rightHom first) (splitRadicalCoordinate splitting second))) +
        cycle (splitRadicalCoordinate splitting first) at relation
    rw [relation, invariant, ← Module.End.mul_apply, ← map_mul, split_coordinate_decomposition]⟩

theorem splitInvariantOneCocycle_inl {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (invariant : ∀ levi radical, cycle (splitting.conjAct levi radical) =
      representation.ρ (splitting levi) (cycle radical)) (radical : N) :
    splitInvariantOneCocycle splitting representation cycle invariant (extension.inl radical) = cycle radical :=
  splitExtendRadicalCycle_inl splitting representation cycle radical

theorem splitInvariantOneCocycle_splitting {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (invariant : ∀ levi radical, cycle (splitting.conjAct levi radical) =
      representation.ρ (splitting levi) (cycle radical)) (levi : L) :
    splitInvariantOneCocycle splitting representation cycle invariant (splitting levi) = 0 :=
  splitExtendRadicalCycle_splitting splitting representation cycle levi

theorem splitInvariantOneCocycle_H1_ne_zero {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (invariant : ∀ levi radical, cycle (splitting.conjAct levi radical) =
      representation.ρ (splitting levi) (cycle radical))
    (nonzero : groupCohomology.H1π (Rep.res extension.inl representation) cycle ≠ 0) :
    groupCohomology.H1π representation (splitInvariantOneCocycle splitting representation cycle invariant) ≠ 0 := by
  intro zero
  obtain ⟨potential, boundary⟩ := (groupCohomology.H1π_eq_zero_iff _).mp zero
  apply nonzero
  apply (groupCohomology.H1π_eq_zero_iff _).mpr
  refine ⟨potential, funext fun radical => ?_⟩
  exact (congrFun boundary (extension.inl radical)).trans
    (splitInvariantOneCocycle_inl splitting representation cycle invariant radical)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
