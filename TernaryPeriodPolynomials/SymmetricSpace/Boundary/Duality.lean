module

public import TernaryPeriodPolynomials.Topology.SingularLocal.DualityDetection
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Inclusions
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionRelative

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryDuality
open CategoryTheory HomologicalComplex IntegralGL3Congruence
open SingularLocalHomology SingularLocalDuality SingularBoundaryRestriction

/-- On the actual compact principal-six quotient, the whole-boundary homology map is onto
iff genuine geometric cohomology restriction with full contragredient coefficients is injective.
This is algebraic universal coefficients; no Poincare--Lefschetz duality is assumed here. -/
theorem boundary_surjective_iff_dual_restriction_injective
    (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    Function.Surjective (homologyMap (boundaryInclusionMap V) n).hom ↔
      Function.Injective (homologyMap (geometricBoundaryRestriction (dualRepresentation V)) n).hom :=
  homologyMap_surjective_iff_dualCohomology_injective
    boundaryProjection bordifiedProjection boundaryInclusion boundaryBaseInclusion boundary_square
    boundaryQuotientCovering bordifiedProjection_quotientCovering boundaryInclusion_equivariant V n

/-- The actual whole-boundary surjectivity gate equals zero of the actual relative-to-absolute
geometric cohomology map with dual coefficients, in the same degree. -/
theorem boundary_surjective_iff_relative_dual_zero
    (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    Function.Surjective (homologyMap (boundaryInclusionMap V) n).hom ↔
      RelativeCochainSequence.relativeMap
        (geometricBoundaryRestriction (dualRepresentation V)) n = 0 := by
  rw [boundary_surjective_iff_dual_restriction_injective]
  exact RelativeCochainSequence.restriction_injective_iff_relativeMap_zero
    (geometricBoundaryRestriction (dualRepresentation V)) n

/-- The literal whole-boundary map into actual group homology, using the singular
resolution comparison of the contractible arithmetic bordification. -/
def boundaryToGroup (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    (boundaryLocalChains V).homology n ⟶ groupHomology V n :=
  homologyMap (boundaryInclusionMap V) n ≫ (bordifiedGroupLocalHomologyIso V n).inv

/-- Boundary surjectivity is unchanged by the genuine compact-quotient/group comparison. -/
theorem boundaryToGroup_surjective_iff (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    Function.Surjective (boundaryToGroup V n).hom ↔
      Function.Surjective (homologyMap (boundaryInclusionMap V) n).hom := by
  let e := (bordifiedGroupLocalHomologyIso V n).symm.toLinearEquiv
  change Function.Surjective (fun x => e ((homologyMap (boundaryInclusionMap V) n).hom x)) ↔ _
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (e y)
    exact ⟨x, e.injective hx⟩
  · intro h
    exact e.surjective.comp h

/-- A precise gate for all-top-boundary: the actual degree-three relative dual map
vanishes exactly when every actual group-homology class comes from the entire boundary. -/
theorem all_top_boundary_iff_relative_dual_zero (V : Rep.{0} ℚ principalSix) :
    Function.Surjective (boundaryToGroup V 3).hom ↔
      RelativeCochainSequence.relativeMap
        (geometricBoundaryRestriction (dualRepresentation V)) 3 = 0 :=
  (boundaryToGroup_surjective_iff V 3).trans (boundary_surjective_iff_relative_dual_zero V 3)

end TernaryPoly.SymmetricSpaceBoundaryDuality
