module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.Reduction

@[expose] public section


/-!
# Lifting the away-three Hecke algebra to global cohomology

Every finite double-coset operator on the maximal boundary coordinates is the restriction of the
same operator on global cohomology. Hence every element of the away-three Hecke algebra lifts
through the restriction map, and a projected restriction `p (R ω)` is the unprojected restriction
`R (p̃ ω)` of another global class.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.Duality

open TernaryPeriodPolynomials.GraphPieces

section Generic

variable {W V : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
  (R : W →ₗ[ℂ] V)

/-- Endomorphisms `A` of `V` such that `A ∘ R = R ∘ lift` for some endomorphism `lift` of `W`
are closed under products. -/
theorem comp_lift_mul {A A' : Module.End ℂ V}
    (hA : ∃ lift : Module.End ℂ W, A.comp R = R.comp lift)
    (hA' : ∃ lift : Module.End ℂ W, A'.comp R = R.comp lift) :
    ∃ lift : Module.End ℂ W, (A * A').comp R = R.comp lift := by
  obtain ⟨lift, hl⟩ := hA
  obtain ⟨lift', hl'⟩ := hA'
  refine ⟨lift * lift', ?_⟩
  change (A.comp A').comp R = R.comp (lift.comp lift')
  rw [LinearMap.comp_assoc, hl', ← LinearMap.comp_assoc, hl, LinearMap.comp_assoc]

theorem comp_lift_add {A A' : Module.End ℂ V}
    (hA : ∃ lift : Module.End ℂ W, A.comp R = R.comp lift)
    (hA' : ∃ lift : Module.End ℂ W, A'.comp R = R.comp lift) :
    ∃ lift : Module.End ℂ W, (A + A').comp R = R.comp lift := by
  obtain ⟨lift, hl⟩ := hA
  obtain ⟨lift', hl'⟩ := hA'
  refine ⟨lift + lift', ?_⟩
  rw [LinearMap.add_comp, LinearMap.comp_add, hl, hl']

theorem comp_lift_algebraMap (scalar : ℂ) :
    ∃ lift : Module.End ℂ W, (algebraMap ℂ (Module.End ℂ V) scalar).comp R = R.comp lift := by
  refine ⟨algebraMap ℂ _ scalar, ?_⟩
  apply LinearMap.ext
  intro x
  simp [Module.algebraMap_end_apply]

end Generic

/-- The unprojected restriction of global cohomology to the maximal boundary coordinates. -/
abbrev globalRestriction (n : ℕ) (χ : RankOneCharacter) :
    WholeGlobalH2 n χ →ₗ[ℂ] BoundaryCoordinates n χ :=
  (Helpers.canonicalCoordinates n χ).comp (Helpers.canonicalRestriction n χ)

/-- The endomorphisms of the boundary coordinates that lift through the global restriction. -/
def liftable (n : ℕ) (χ : RankOneCharacter) :
    Subalgebra ℂ (Module.End ℂ (BoundaryCoordinates n χ)) where
  carrier := {A | ∃ lift : Module.End ℂ (WholeGlobalH2 n χ),
    A.comp (globalRestriction n χ) = (globalRestriction n χ).comp lift}
  mul_mem' := fun {_ _} hA hA' => comp_lift_mul (globalRestriction n χ) hA hA'
  add_mem' := fun {_ _} hA hA' => comp_lift_add (globalRestriction n χ) hA hA'
  algebraMap_mem' scalar := comp_lift_algebraMap (globalRestriction n χ) scalar

/-- Every pair Hecke operator lifts through the global restriction. -/
theorem pairHecke_mem_liftable {n : ℕ} (D : InducingData n) (t : HeckeCorrespondence) :
    pairHecke D (Reduction.canonicalStratumHecke n D.chi) t ∈ liftable n D.chi :=
  ⟨Helpers.canonicalHecke (rationalCoefficientComponent n D.chi) t,
    (Helpers.canonicalCoordinates_restriction_hecke n D.chi t).symm⟩

/-- The away-three Hecke algebra lifts through the global restriction. -/
theorem awayThreeHeckeAlgebra_le_liftable {n : ℕ} (D : InducingData n) :
    awayThreeHeckeAlgebra D (Reduction.canonicalStratumHecke n D.chi) ≤ liftable n D.chi := by
  apply Algebra.adjoin_le
  rintro A ⟨t, -, rfl⟩
  exact pairHecke_mem_liftable D t

/-- An element of the away-three Hecke algebra applied to a restriction is a restriction. -/
theorem exists_restriction_lift {n : ℕ} (D : InducingData n)
    {projection : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (membership : projection ∈ awayThreeHeckeAlgebra D (Reduction.canonicalStratumHecke n D.chi)) :
    ∃ lift : Module.End ℂ (WholeGlobalH2 n D.chi), ∀ globalClass,
      Reduction.projectedRestriction D projection globalClass =
        globalRestriction n D.chi (lift globalClass) := by
  obtain ⟨lift, equation⟩ := awayThreeHeckeAlgebra_le_liftable D membership
  exact ⟨lift, fun globalClass => LinearMap.congr_fun equation globalClass⟩

end TernaryPeriodPolynomials.Duality
