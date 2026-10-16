module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Isotropy
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.GraphReduction

@[expose] public section


/-!
# Half-dimension from global top vanishing and boundary duality

No global class projects to `(0, b)` with `b ≠ 0`. The projector of the away-three Hecke algebra
lifts to global cohomology, so it suffices to treat unprojected restrictions `(0, b)` with `b` in
the line summand. For such a class and any global class `ω'` with plane restriction `ξ`, the
boundary cup product of `b` with `ξ` is exact (`boundaryExact_of_plane_zero`, using `H⁴(Γ, ℂ) = 0`),
while boundary duality on the associate pair makes it non-exact for a suitable `ξ` unless `b = 0`.
Global classes with every plane restriction exist by the Eisenstein classes of the standard graph.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.Duality

open TernaryPeriodPolynomials.GraphPieces
open TernaryPeriodPolynomials.EisensteinGraph

variable {n : ℕ} (D : InducingData n) (φ : RationalGL3 →* RationalGL3)
  (level : ∀ g ∈ rationalLevel, φ g ∈ rationalLevel)
  (B : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ)
  (invariant : ∀ g ∈ rationalLevel, ∀ v w,
    B (rationalCoefficientComponent n D.chi g v)
      (rationalCoefficientComponent n D.chi (φ g) w) = B v w)
  (dualFlag : Flags .line → Flags .plane)

include level invariant in
/-- Unprojected half-dimension: a global class whose plane restriction vanishes and whose line
restriction lies in the line summand has vanishing line restriction. -/
theorem line_eq_zero_of_associateDuality (top : CupProductExactness D φ B)
    (duality : AssociateDuality D φ dualFlag B)
    (planeSurjective : ∀ ξ ∈ boundarySummand D .plane,
      ∃ globalClass, (globalRestriction n D.chi globalClass).1 = ξ)
    (globalClass : WholeGlobalH2 n D.chi)
    (planeZero : (globalRestriction n D.chi globalClass).1 = 0)
    (lineSummand : (globalRestriction n D.chi globalClass).2 ∈ boundarySummand D .line) :
    (globalRestriction n D.chi globalClass).2 = 0 := by
  by_contra nonzero
  obtain ⟨ξ, ξmem, detects⟩ := duality _ lineSummand nonzero
  obtain ⟨dualClass, dualPlane⟩ := planeSurjective ξ ξmem
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ globalClass
  obtain ⟨c', rfl⟩ := Submodule.mkQ_surjective _ dualClass
  have restriction := globalRestriction_classOf D c
  have dualRestriction := globalRestriction_classOf D c'
  change globalRestriction n D.chi (classOf rationalLevel (rationalCoefficientComponent n D.chi) c) = _ at restriction
  change globalRestriction n D.chi (classOf rationalLevel (rationalCoefficientComponent n D.chi) c') = _ at dualRestriction
  change (globalRestriction n D.chi (classOf rationalLevel (rationalCoefficientComponent n D.chi) c)).1 = 0 at planeZero
  change (globalRestriction n D.chi (classOf rationalLevel (rationalCoefficientComponent n D.chi) c')).1 = ξ at dualPlane
  change ¬ (globalRestriction n D.chi (classOf rationalLevel (rationalCoefficientComponent n D.chi) c)).2 = 0 at nonzero
  rw [restriction] at planeZero
  rw [dualRestriction] at dualPlane
  have boundary := (Submodule.Quotient.mk_eq_zero _).mp planeZero
  obtain ⟨u, primitive⟩ := boundary
  obtain ⟨γ, γmem, γprimitive, exactCup⟩ :=
    boundaryExact_of_plane_zero D φ level B invariant top dualFlag c c' u primitive
  refine detects (restrictionCocycle n D.chi .line c) ?_ (planeEdgeCochain D u) ?_
    (restrictionCocycle n D.chi .plane c') dualPlane γ γmem γprimitive exactCup
  · change _ = (globalRestriction n D.chi (classOf rationalLevel (rationalCoefficientComponent n D.chi) c)).2
    rw [restriction]
  · intro x e
    exact (congrFun (congrArg (fun z => z.val.val x) primitive) (endpoint .plane e)).symm

omit level invariant in
include level invariant in
/-- Half-dimension for a projector of the away-three Hecke algebra onto the associate pair, given
global classes with every plane summand class as projected plane restriction, `H⁴(Γ, ℂ) = 0`, and
boundary duality on the associate pair. -/
theorem halfDimension_of_associateDuality
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (membership : projection ∈ awayThreeHeckeAlgebra D (Reduction.canonicalStratumHecke n D.chi))
    (range : LinearMap.range projection ≤ associatePair D)
    (planeSurjective : ∀ ξ ∈ boundarySummand D .plane,
      ∃ globalClass, (Reduction.projectedRestriction D projection globalClass).1 = ξ)
    (top : CupProductExactness D φ B) (duality : AssociateDuality D φ dualFlag B) :
    GraphReduction.HalfDimension D projection := by
  obtain ⟨lift, lifts⟩ := exists_restriction_lift D membership
  intro globalClass planeZero
  rw [lifts] at planeZero ⊢
  have inPair : Reduction.projectedRestriction D projection globalClass ∈ associatePair D :=
    range ⟨_, rfl⟩
  rw [lifts] at inPair
  refine line_eq_zero_of_associateDuality D φ level B invariant dualFlag top duality ?_
    (lift globalClass) planeZero inPair.2
  intro ξ ξmem
  obtain ⟨dualClass, dualPlane⟩ := planeSurjective ξ ξmem
  exact ⟨lift dualClass, by rw [← lifts]; exact dualPlane⟩

omit level invariant in
include level invariant in
/-- The Eisenstein classes of the standard graph give every plane summand class as a projected
plane restriction, so half-dimension follows from `H⁴(Γ, ℂ) = 0` and boundary duality. -/
theorem halfDimension_of_eisensteinClasses
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (membership : projection ∈ awayThreeHeckeAlgebra D (Reduction.canonicalStratumHecke n D.chi))
    (range : LinearMap.range projection ≤ associatePair D)
    (existsIntegral : ∀ plane : StandardConstruction.SourceSpace.sourceCocycles D .plane,
      ∃ line, StandardConstruction.StandardRelation.Related D plane line)
    (eisenstein : GraphReduction.HasEisensteinClasses D projection)
    (top : CupProductExactness D φ B) (duality : AssociateDuality D φ dualFlag B) :
    GraphReduction.HalfDimension D projection := by
  refine halfDimension_of_associateDuality D φ level B invariant dualFlag projection membership
    range ?_ top duality
  intro ξ ξmem
  obtain ⟨plane, planeEq⟩ :=
    StandardConstruction.SourceQuotient.sourceToSummand_surjective D .plane ⟨ξ, ξmem⟩
  refine ⟨eisenstein.choose plane, ?_⟩
  rw [eisenstein.choose_spec plane (existsIntegral plane).choose (existsIntegral plane).choose_spec]
  exact congrArg Subtype.val planeEq

end TernaryPeriodPolynomials.Duality
