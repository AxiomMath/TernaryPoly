module

public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionCochains
public import TernaryPeriodPolynomials.GroupCohomology.Relative.CochainSequence

@[expose] public section


noncomputable section
open CategoryTheory Limits HomologicalComplex
namespace TernaryPoly.SingularBoundaryRestriction
open IntegralGL3Congruence

/-- The actual boundary restriction is an epimorphism of genuine cochain complexes. -/
instance boundaryRestriction_epi (V : Rep ℚ principalSix) : Epi (boundaryRestriction V) :=
  epi_of_epi_f _ (fun n => (ModuleCat.epi_iff_surjective _).mpr (boundaryRestriction_surjective V n))

/-- The genuine relative cochain complex for the actual bordification and its boundary. -/
abbrev relativeCochains (V : Rep ℚ principalSix) := RelativeCochainSequence.relative (boundaryRestriction V)

/-- The actual relative-to-absolute cochain inclusion. -/
abbrev relativeInclusion (V : Rep ℚ principalSix) : relativeCochains V ⟶ absoluteCochains V :=
  RelativeCochainSequence.inclusion (boundaryRestriction V)

/-- The actual boundary restriction gives a short exact relative/absolute/boundary sequence. -/
theorem boundary_shortExact (V : Rep ℚ principalSix) :
    (RelativeCochainSequence.sequence (boundaryRestriction V)).ShortExact :=
  RelativeCochainSequence.shortExact (boundaryRestriction V)

abbrev relativeToAbsolute (V : Rep ℚ principalSix) (n : ℕ) :=
  RelativeCochainSequence.relativeMap (boundaryRestriction V) n

abbrev restrictionOnCohomology (V : Rep ℚ principalSix) (n : ℕ) :=
  RelativeCochainSequence.restrictionMap (boundaryRestriction V) n

abbrev boundaryConnecting (V : Rep ℚ principalSix) (n : ℕ) :=
  RelativeCochainSequence.connecting (boundaryRestriction V) n

/-- The actual relative image is precisely the kernel of literal geometric boundary restriction. -/
theorem relative_range_eq_boundary_kernel (V : Rep ℚ principalSix) (n : ℕ) :
    LinearMap.range (relativeToAbsolute V n).hom=LinearMap.ker (restrictionOnCohomology V n).hom :=
  RelativeCochainSequence.range_relative_eq_kernel (boundaryRestriction V) n

/-- An actual absolute class restricts to zero precisely when it admits a relative lift. -/
theorem boundary_zero_iff_relative_lift (V : Rep ℚ principalSix) (n : ℕ)
    (x : (absoluteCochains V).homology n) :
    restrictionOnCohomology V n x=0 ↔ ∃ y,relativeToAbsolute V n y=x :=
  RelativeCochainSequence.restriction_zero_iff_lifts (boundaryRestriction V) n x

/-- Exactness at the actual boundary cohomology term. -/
theorem boundary_range_eq_connecting_kernel (V : Rep ℚ principalSix) (n : ℕ) :
    LinearMap.range (restrictionOnCohomology V n).hom=LinearMap.ker (boundaryConnecting V n).hom :=
  RelativeCochainSequence.range_restriction_eq_kernel_connecting (boundaryRestriction V) n

/-- Exactness at the subsequent relative cohomology term. -/
theorem connecting_range_eq_relative_kernel (V : Rep ℚ principalSix) (n : ℕ) :
    LinearMap.range (boundaryConnecting V n).hom=LinearMap.ker (relativeToAbsolute V (n+1)).hom :=
  RelativeCochainSequence.range_connecting_eq_kernel_relative (boundaryRestriction V) n

/-- The independent inner-cohomology vanishing obligation remains explicit. -/
theorem boundary_injective_iff_relative_zero (V : Rep ℚ principalSix) (n : ℕ) :
    Function.Injective (restrictionOnCohomology V n) ↔ relativeToAbsolute V n=0 :=
  RelativeCochainSequence.restriction_injective_iff_relativeMap_zero (boundaryRestriction V) n

/-- Literal geometric local-system boundary restriction is also an epi of cochain complexes. -/
instance geometricBoundaryRestriction_epi (V : Rep ℚ principalSix) :
    Epi (geometricBoundaryRestriction V) :=
  epi_of_epi_f _ (fun n => (ModuleCat.epi_iff_surjective _).mpr
    (geometricBoundaryRestriction_surjective V n))

/-- The actual relative complex in the downstairs geometric local-coefficient model. -/
abbrev geometricRelativeCochains (V : Rep ℚ principalSix) :=
  RelativeCochainSequence.relative (geometricBoundaryRestriction V)

/-- The actual geometric local-coefficient relative sequence is short exact. -/
theorem geometricBoundary_shortExact (V : Rep ℚ principalSix) :
    (RelativeCochainSequence.sequence (geometricBoundaryRestriction V)).ShortExact :=
  RelativeCochainSequence.shortExact (geometricBoundaryRestriction V)

/-- Exactness at actual geometric local-system absolute cohomology. -/
theorem geometric_relative_range_eq_boundary_kernel (V : Rep ℚ principalSix) (n : ℕ) :
    LinearMap.range (RelativeCochainSequence.relativeMap (geometricBoundaryRestriction V) n).hom=
      LinearMap.ker (RelativeCochainSequence.restrictionMap (geometricBoundaryRestriction V) n).hom :=
  RelativeCochainSequence.range_relative_eq_kernel (geometricBoundaryRestriction V) n

end TernaryPoly.SingularBoundaryRestriction
