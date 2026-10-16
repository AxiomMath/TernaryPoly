module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Levi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.IdentityPlaneCoordinate

@[expose] public section


/-!
# The period input of the identity-plane coordinate

For a spherical inducing datum the Levi cocycle data built from the Hecke-eigenvector Eichler input
has nonzero arithmetic period class, which is the input `PeriodNonvanishing` of the identity-plane
coordinate (`IdentityPlaneCoordinate`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic

/-- **The period input holds for every spherical datum.** The hypothesis on the character is not
needed: the period class only involves the cuspidal part. -/
theorem periodNonvanishing_of_spherical {n : ℕ} (D : InducingData n)
    (_hchi : D.chi = trivialCharacter) (hsph : SphericalCusp D.cusp) : PeriodNonvanishing D := by
  have odd : Odd n :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd
      n D.cusp D.cohomological hsph
  obtain ⟨E, φ, hφ, nonzero⟩ := exists_leviCocycleData_period_ne_zero D hsph odd
  unfold PeriodNonvanishing
  exact ⟨E, φ, hφ, nonzero⟩

/-- The period input as the implication consumed by `sphericalSourceConstruction_of_period`. -/
theorem periodNonvanishing_of_spherical_imp {n : ℕ} (D : InducingData n)
    (hchi : D.chi = trivialCharacter) : SphericalCusp D.cusp → PeriodNonvanishing D :=
  fun hsph => periodNonvanishing_of_spherical D hchi hsph

end TernaryPeriodPolynomials.SourceConstruction

end
