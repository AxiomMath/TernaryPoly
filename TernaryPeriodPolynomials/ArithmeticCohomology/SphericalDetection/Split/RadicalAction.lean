module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OneCocyclePullback
public import Mathlib.GroupTheory.GroupExtension.Basic

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

def splitRadicalInput {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (element : L) : N →* N :=
  (splitting.conjAct element⁻¹).toMonoidHom

theorem splitRadicalInput_one {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (radical : N) : splitRadicalInput splitting 1 radical = radical := by
  simp [splitRadicalInput]

theorem splitRadicalInput_mul {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (first second : L) (radical : N) :
    splitRadicalInput splitting (first * second) radical =
      splitRadicalInput splitting second (splitRadicalInput splitting first radical) := by
  simp [splitRadicalInput, mul_inv_rev]

theorem splitRadicalInput_commute {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (element : L) (radical : N) :
    extension.inl radical * splitting element =
      splitting element * extension.inl (splitRadicalInput splitting element radical) := by
  have conjugation := extension.inl_conjAct_comm (e := splitting element⁻¹) (n := radical)
  change extension.inl (splitRadicalInput splitting element radical) =
    splitting element⁻¹ * extension.inl radical * (splitting element⁻¹)⁻¹ at conjugation
  rw [map_inv, inv_inv] at conjugation
  simp only [conjugation, ← mul_assoc, mul_inv_cancel, one_mul]

theorem splitRadicalCoefficient_intertwines {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E) (element : L) (radical : N) :
    ((Rep.res extension.inl representation).ρ radical).comp (representation.ρ (splitting element)) =
      (representation.ρ (splitting element)).comp
        ((Rep.res extension.inl representation).ρ (splitRadicalInput splitting element radical)) := by
  change representation.ρ (extension.inl radical) * representation.ρ (splitting element) =
    representation.ρ (splitting element) * representation.ρ (extension.inl (splitRadicalInput splitting element radical))
  rw [← map_mul, ← map_mul, splitRadicalInput_commute]

def splitRadicalCocycleAction {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E) (element : L) :
    groupCohomology.cocycles₁ (Rep.res extension.inl representation) →ₗ[ℂ]
      groupCohomology.cocycles₁ (Rep.res extension.inl representation) :=
  oneCocyclePullback (Rep.res extension.inl representation) (Rep.res extension.inl representation)
    (splitRadicalInput splitting element) (representation.ρ (splitting element))
    (splitRadicalCoefficient_intertwines splitting representation element)

theorem splitRadicalCocycleAction_apply {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E) (element : L)
    (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation)) (radical : N) :
    splitRadicalCocycleAction splitting representation element cycle radical =
      representation.ρ (splitting element) (cycle (splitRadicalInput splitting element radical)) := rfl

theorem splitRadicalCocycleAction_one {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation)) :
    splitRadicalCocycleAction splitting representation 1 cycle = cycle := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  rw [splitRadicalCocycleAction_apply, splitRadicalInput_one, map_one, map_one, Module.End.one_apply]

theorem splitRadicalCocycleAction_mul {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E) (first second : L)
    (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation)) :
    splitRadicalCocycleAction splitting representation (first * second) cycle =
      splitRadicalCocycleAction splitting representation first
        (splitRadicalCocycleAction splitting representation second cycle) := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  simp only [splitRadicalCocycleAction_apply, splitRadicalInput_mul, map_mul, Module.End.mul_apply]

def splitRadicalH1Action {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E) (element : L) :
    Module.End ℂ (groupCohomology.H1 (Rep.res extension.inl representation)) :=
  oneCocyclePullbackH1 (Rep.res extension.inl representation) (Rep.res extension.inl representation)
    (splitRadicalInput splitting element) (representation.ρ (splitting element))
    (splitRadicalCoefficient_intertwines splitting representation element)

theorem splitRadicalH1Action_apply {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E) (element : L)
    (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation)) :
    splitRadicalH1Action splitting representation element
        (groupCohomology.H1π (Rep.res extension.inl representation) cycle) =
      groupCohomology.H1π (Rep.res extension.inl representation)
        (splitRadicalCocycleAction splitting representation element cycle) :=
  oneCocyclePullbackH1_apply (Rep.res extension.inl representation) (Rep.res extension.inl representation)
    (splitRadicalInput splitting element) (representation.ρ (splitting element))
    (splitRadicalCoefficient_intertwines splitting representation element) cycle

def splitRadicalH1Representation {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E) : Rep ℂ L :=
  Rep.of {
    toFun := splitRadicalH1Action splitting representation
    map_one' := by
      apply LinearMap.ext
      intro cohomology
      obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (Rep.res extension.inl representation) cohomology
      rw [splitRadicalH1Action_apply, splitRadicalCocycleAction_one]
      rfl
    map_mul' first second := by
      apply LinearMap.ext
      intro cohomology
      obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (Rep.res extension.inl representation) cohomology
      change splitRadicalH1Action splitting representation (first * second) _ =
        splitRadicalH1Action splitting representation first (splitRadicalH1Action splitting representation second _)
      rw [splitRadicalH1Action_apply, splitRadicalH1Action_apply, splitRadicalH1Action_apply, splitRadicalCocycleAction_mul] }

end TernaryPeriodPolynomials.SphericalDetection.Helpers
