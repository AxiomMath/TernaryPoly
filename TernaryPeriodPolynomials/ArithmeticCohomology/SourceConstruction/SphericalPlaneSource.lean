module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Plane
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.IdentityPlaneCoordinate

@[expose] public section


/-!
# The spherical plane source construction for the trivial character

For `D.chi = 1` and a spherical `D`, the plane source cocycle built from the Eichler cocycle of the
Hecke eigenvector has nonzero Shapiro coordinate at the identity plane. This discharges the
construction inputs S1 (`SphericalSourceConstruction`) and N3 (`SphericalIdentityPlaneSource`) of
the separation argument for the trivial character, with no hypothesis on the associate pair.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.SourceConstruction

variable {n : ℕ}

/-- **S1 for the trivial character.** -/
theorem sphericalSourceConstruction_of_trivial (D : InducingData n)
    (hchi : D.chi = trivialCharacter) : SphericalSourceConstruction D :=
  sphericalSourceConstruction_of_period D hchi (periodNonvanishing_of_spherical_imp D hchi)

/-- **N3 for the trivial character.** -/
theorem sphericalIdentityPlaneSource_of_trivial (D : InducingData n)
    (hchi : D.chi = trivialCharacter) : SphericalIdentityPlaneSource D :=
  sphericalIdentityPlaneSource_of_period D hchi (periodNonvanishing_of_spherical_imp D hchi)

/-- The form consumed by the spectral targets. -/
theorem sphericalSourceConstruction_of_trivial_ne (D : InducingData n) :
    D.chi = trivialCharacter → associatePair D ≠ ⊥ → SphericalSourceConstruction D :=
  fun hchi _ => sphericalSourceConstruction_of_trivial D hchi

end TernaryPeriodPolynomials.SourceConstruction
